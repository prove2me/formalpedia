-- Prove2me | Theorems.Thm_LiftSAParity_Supplement_theorem_5_4
-- name    : LiftSAParity.Supplement.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:16:04.053844+00:00
-- url     : https://prove2.me/theorems/52c152b0-6f00-43cc-a543-bd37f321f022
-- title:
--   Theorem 5.4 — an $(r,t,\varepsilon)$-fooling local distribution forces semantic SA(⊕) coefficient size $\ge1/\varepsilon$
-- statement:
--   Let $\varphi$ be an unsatisfiable CNF formula over $n$ blocks of $\ell$ variables, let $r,t,d\in\mathbb N$ with $rt\le d$ and $t\ge1$, and let $\varepsilon>0$. Suppose $\varphi$ admits an $(r,t,\varepsilon)$-fooling block $d$-local distribution $\mathcal D$. Then every semantic SA(⊕) refutation $\pi$ of $\varphi$ satisfies
--   $$
--   \mathrm{coeffSize}(\pi)\ \ge\ \frac1\varepsilon .
--   $$
--
--   This is the gadget-free lower bound of the paper (the formal version of the informal Theorem 1.3): a local distribution that looks uniform to every $t$-safe linear system of codimension at most $r$, even after conditioning on assignments in its support, already rules out small refutations. Since semantic SA(⊕) subsumes SA(⊕), it also bounds the size of uSA(⊕) refutations.
--
--   **Formalization Note** $\mathcal D$ is a block $d$-local distribution (`IsBlockLocalDist`), and fooling is `IsFooling` (Definition 5.3). The bound is exactly $1/\varepsilon$, with no constant loss.
--
--   Differences from the source:
--   - reading: r, t, d ∈ ℕ → the extra hypothesis 1 ≤ t (ℕ read as {1, 2, …} for t); reason: the proof says "Since t ≥ 1" (p.19), and at t = 0 the printed statement is false: for φ = {x₁, ¬x₁} (n = ℓ = 1), d = 0, t = 0, r = 2, condition (1) holds exactly (I = ∅, uniform sampling) and condition (2) is vacuous (no affine space has codimension 2), so every ε > 0 is admissible while φ has a fixed-size refutation
--   - encoding: d-local distribution with variables replaced by blocks → IsBlockLocalDist (|I| counts blocks, assignments in 𝔽₂); reason: Lean convention for the paper's object; same instances
--   - encoding: Cl^t(A), the unique inclusion-minimal set of blocks outside which A is t-safe → the intersection of all such sets; reason: equal for every nonempty affine A by the proof of Lemma 5.1
--   - generalization: integers n, ℓ ≥ 1 (§2, p.7) → n, ℓ : ℕ, including 0; reason: if n = 0 or ℓ = 0 there is one total assignment, an unsatisfiable φ contains the empty clause, and no block d-local distribution exists (D_∅'s only assignment falsifies it), so the extra cases are vacuous
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §5.3, Theorem 5.4, p.18 (informal version Theorem 1.3, p.5)

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_LiftSAParity_SemSAXorRefutation
import Definitions.Def_LiftSAParity_Supplement_IsFooling

namespace LiftSAParity

namespace Supplement

/-- **Theorem 5.4** (de Rezende–Engström–Shekhovtsov, *Lifting Sherali-Adams Degree to Unary
Sherali-Adams over Parities Size*, manuscript (sha256 cab5a032…), §5.3, p.18; informal version
Theorem 1.3, p.5): "Let φ be an unsatisfiable CNF formula, r, t, d ∈ ℕ with rt ≤ d, and ε > 0 be
such that φ admits an (r, t, ε)-fooling d-local distribution D. Then, any semantic SA(⊕)
refutation of φ has coefficient size at least 1/ε."

**Formalization Note** `φ` is a CNF over `n` blocks of `ℓ` variables and `D` is a block d-local
distribution (`|I|` counts blocks). The hypothesis `1 ≤ t` reads `ℕ` as `{1, 2, …}` for `t`: the
proof uses "Since t ≥ 1" (p.19), and at `t = 0` the printed statement fails (`Cl⁰(A) = ∅`, so
condition (2) holds with `ε = 2^{−r}` for every formula). -/
theorem theorem_5_4 (n ℓ : ℕ) (φ : CNF (Fin n × Fin ℓ)) (r t d : ℕ) (ε : ℝ)
    (D : (I : Finset (Fin n)) → BlockAssign n ℓ I → ℝ)
    (hunsat : ¬ Satisfiable φ) (hrt : r * t ≤ d) (hε : 0 < ε) (ht : 1 ≤ t)
    (hD : IsFooling φ d r t ε D) :
    ∀ π : SemSAXorRefutation φ, 1 / ε ≤ π.coeffSize := by sorry

end Supplement

end LiftSAParity
