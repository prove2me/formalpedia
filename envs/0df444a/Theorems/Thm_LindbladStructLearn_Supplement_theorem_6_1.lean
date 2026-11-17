-- Prove2me | Theorems.Thm_LindbladStructLearn_Supplement_theorem_6_1
-- name    : LindbladStructLearn.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:48:03.658742+00:00
-- url     : https://prove2.me/theorems/49a77206-2df8-4441-bb46-35ac1ca0136b
-- title:
--   Theorem 6.1 — lower bound $\Omega(gd^2/(\varepsilon^2\log d))$ on the total evolution time of adaptive learners with ancillas
-- statement:
--   There is an absolute constant $c>0$ such that the following holds. Let $m\ge10^8$ be an integer, $g>0$ and $0<\varepsilon\le g/512$, and set $n=m^3+1$ and $d=6m+1$. There is a finite nonempty family $\mathcal C_{m,g,\varepsilon}$ of valid two-local Lindbladians on $n$ qubits such that every $\mathcal L\in\mathcal C_{m,g,\varepsilon}$ satisfies
--   $$\frac g2\le\|\mathcal L\|_{B_1}\le g,\qquad \frac m2\le\deg_{\varepsilon/25600}(\mathcal L)\le\deg(\mathcal L)\le d.$$
--   Consider any learning algorithm: it may query the dynamics adaptively, use ancillary systems of any finite dimension and entangled operations and measurements, and finally output estimates of all coefficients. Suppose it learns the coefficients of every $\mathcal L\in\mathcal C_{m,g,\varepsilon}$ to error $\varepsilon$ in $\infty$-norm with probability at least $0.99$. Then its total evolution time $T$ satisfies
--   $$T\ \ge\ c\,\frac{g\,m^2}{\varepsilon^2\log m}\qquad\text{and}\qquad T\ \ge\ c\,\frac{g\,d^2}{\varepsilon^2\log d}.$$
--
--   The upper bound of Theorem 1.1 is $O(gd^2\log n/\varepsilon^2)$, so this shows it is optimal up to logarithmic factors, even against adaptive, entangled learners (informally Theorem 1.2).
--
--   **Formalization Note** A learner is an admissible public bounded-query protocol (`LindbladTolerant.Testing.Protocol`) together with a measurable estimator of its outcome history. Its success probability is `learnSuccess`. Its total evolution time is any $T$ bounding the sum of the durations on every complete outcome branch (`TimeAtMost`). The bound $m/2\le\deg_{\varepsilon/25600}(\mathcal L)$ is stated as: every $d'$ with $\deg_{\varepsilon/25600}(\mathcal L)\le d'$ has $m/2\le d'$.
--
--   Differences from the source:
--   - encoding: there exists a finite family C_{m,g,ε} of two-local Lindbladians → a nonempty Finset of coefficient vectors that are valid (IsLindbladParams) and two-local (IsKLocal 2); reason: an empty family would make the lower bound vacuous; the paper's family is nonempty (6.18)–(6.21)
--   - encoding: m/2 ≤ deg_{ε/25600}(L) ≤ deg(L) ≤ d → every d′ with ApproxDegLe (ε/25600) λ d′ has m/2 ≤ d′, and deg λ ≤ 6m + 1; reason: the published approximate degree is the ∃ form deg_η(L) ≤ d′; deg_η(L) ≤ deg(L) holds for every η > 0
--   - reading: any learning algorithm (adaptive, with ancillas, entangled operations and measurements, p.53) → any admissible protocol LindbladTolerant.Testing.Protocol with a measurable estimator of its outcome history; reason: the protocol has adaptive durations t ≥ 0, a memory of any finite dimension, CP instruments with outcomes in any measurable space (of any universe) and finitely many queries (the proof of Proposition 6.7, p.64, assumes N queries); measurability is what makes the success probability defined
--   - reading: must use a total evolution time t_total = Ω(·) → every T with TimeAtMost p T (the durations sum to at most T on every complete outcome branch) satisfies the bounds; reason: the proof (p.64) simulates the learner from the program state Ψ_u(T), which requires every branch to evolve for total time at most T
--   - encoding: Ω(gm²/(ε² log m)) = Ω(gd²/(ε² log d)) → c·g·m²/(ε² log m) ≤ T and c·g·d²/(ε² log d) ≤ T with one absolute c > 0; reason: Ω(·) as an explicit absolute constant; both forms are stated
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 6.1, p.53 (informal Theorem 1.2, p.4); family (6.17)–(6.21), p.55; proof pp.53–74

import Mathlib
import Definitions.Def_LindbladStructLearn_Supplement_Learner
import Definitions.Def_LindbladStructLearn_IsLindbladParams
import Definitions.Def_LindbladStructLearn_IsKLocal
import Definitions.Def_LindbladStructLearn_b1Norm
import Definitions.Def_LindbladStructLearn_deg
import Definitions.Def_LindbladStructLearn_ApproxDegLe

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal

namespace LindbladStructLearn.Supplement

universe u

open LindbladTolerant.Testing LindbladStructLearn

/-- Theorem 6.1 (lower bound; Lewis–Tang–Wright, *Learning the structure of open quantum systems*,
arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), p.53; informal Theorem 1.2, p.4). Let
`m ≥ 10⁸` be an integer, `g > 0`, `0 < ε ≤ g/512`, `n = m³ + 1`, `d = 6m + 1`. There is a finite
family `C_(m,g,ε)` of two-local Lindbladians on `n` qubits such that every `L` in it satisfies
`g/2 ≤ ‖L‖_B1 ≤ g` and `m/2 ≤ deg_(ε/25600)(L) ≤ deg(L) ≤ d`, and any learning algorithm which learns
the coefficients of every `L ∈ C_(m,g,ε)` to `ε`-error in `∞`-norm with probability at least `0.99`
must use total evolution time `Ω(g m²/(ε² log m)) = Ω(g d²/(ε² log d))`.

**Formalization Note**
1. The family is a nonempty `Finset` of valid (`IsLindbladParams`), two-local coefficient vectors; an
   empty family would make the lower bound vacuous. `m/2 ≤ deg_(ε/25600)(L)` is stated as: every `d'`
   with `deg_(ε/25600)(L) ≤ d'` (the published `ApproxDegLe`) has `m/2 ≤ d'`.
2. A learning algorithm is any admissible public bounded-query protocol
   (`LindbladTolerant.Testing.Protocol`: adaptive durations `t ≥ 0`, an ancillary memory of any finite
   dimension, entangled instruments with outcomes in a measurable space of any universe, finitely many queries) with a
   measurable estimator `est` of the outcome history; its success probability is `learnSuccess`
   (every coefficient `λ_(P₁,P₂)`, `P₁ ≠ I`, within `ε`).
3. Total evolution time is the sum of the durations on every complete outcome branch
   (`TimeAtMost p T`); the conclusion bounds every such `T`. `Ω(·)` is an absolute constant `c > 0`. -/
theorem theorem_6_1 :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 10 ^ 8 ≤ m → ∀ g : ℝ, 0 < g → ∀ ε : ℝ, 0 < ε → ε ≤ g / 512 →
      ∃ fam : Finset (Pauli (m ^ 3 + 1) × Pauli (m ^ 3 + 1) → ℂ), fam.Nonempty ∧
        (∀ lam ∈ fam, IsLindbladParams lam ∧ IsKLocal 2 lam ∧
          g / 2 ≤ b1Norm lam ∧ b1Norm lam ≤ g ∧
          (∀ d' : ℕ, ApproxDegLe (ε / 25600) lam d' → (m : ℝ) / 2 ≤ d') ∧
          deg lam ≤ 6 * m + 1) ∧
        ∀ (Ω : Type u) [MeasurableSpace Ω] (p : Protocol (m ^ 3 + 1) Ω),
          LindbladTolerant.Testing.Admissible p →
          ∀ est : List Ω → Pauli (m ^ 3 + 1) × Pauli (m ^ 3 + 1) → ℂ,
          (∀ r : ℕ, Measurable (fun h : Fin r → Ω => est (List.ofFn h))) →
          (∀ lam ∈ fam, (99 / 100 : ℝ≥0∞) ≤ learnSuccess p est ε lam) →
          ∀ T : ℝ, TimeAtMost p T →
            c * g * (m : ℝ) ^ 2 / (ε ^ 2 * Real.log m) ≤ T ∧
            c * g * ((6 * m + 1 : ℕ) : ℝ) ^ 2 / (ε ^ 2 * Real.log ((6 * m + 1 : ℕ) : ℝ)) ≤ T := by sorry

end LindbladStructLearn.Supplement
