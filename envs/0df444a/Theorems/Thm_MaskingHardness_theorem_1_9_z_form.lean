-- Prove2me | Theorems.Thm_MaskingHardness_theorem_1_9_z_form
-- name    : MaskingHardness.theorem_1_9_z_form
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:52:00.979178+00:00
-- url     : https://prove2.me/theorems/e0d19bb6-d3c7-4a7b-8e63-66932087e3a8
-- title:
--   Proof of Theorem 1.9, p.22 — $\inf_\lambda$ regularized loss $=\max_{z:\mathcal X\times\mathcal Y\to\Delta_k}\mathbb E[h(y,z)]$ under the pseudorandomness constraints
-- statement:
--   Let $\mathcal X$ be finite, $\mathcal Y=[k]$, $\mathcal D$ a distribution over $\mathcal X\times\mathcal Y$, $\mathcal C$ a finite collection of functions $\mathcal X\to\mathbb R^k$, $g:\mathcal Y\times\mathbb R^k\to\mathbb R$ and $h:\mathcal Y\times\Delta_k\to\overline{\mathbb R}$ convex–concave conjugates, and $\varepsilon\ge0$. Then
--
--   $$
--   \inf_{\lambda\in\mathbb R^{\mathcal C}}\mathbb E\bigl[g(y,\pi(c_\lambda(x)))\bigr]+\varepsilon\|\lambda\|_1=\max_{z:\mathcal X\times\mathcal Y\to\Delta_k}\mathbb E\bigl[h(y,z(x,y))\bigr]\quad\text{s.t.}\quad\forall c\in\mathcal C,\ \bigl|\mathbb E[\langle c(x),z(x,y)-\vec 1/k\rangle]\bigr|\le\varepsilon,
--   $$
--
--   and the maximum on the right is attained by a feasible $z$.
--
--   This is the form produced by applying Theorem 3.3 to $g_1,h_1$ (Lemma A.1) and $R,S$ (Lemma A.2); the main theorem follows by reading $z(x,e_j)$ as the $j$-th column of a channel matrix.
--
--   **Formalization Note** "max" is `IsGreatest` of the set of values of feasible $z$, with the left-hand infimum taken in `EReal`; expectations of $h$ are `EReal` weighted sums.
--
--   Differences from the source:
--   - generalization: a finite set C ⊆ {X → ℝᵏ} → a finite indexed family c : ι → X → ℝᵏ, repetitions allowed; reason: the paper's set C is the family indexed by its own elements (ι = C, c = inclusion), so the statement specializes to the source's
--   - encoding: a distribution D over X × Y → weights D x y ≥ 0 summing to 1 (IsDist); expectations are the weighted finite sums; reason: finite sets; same distributions, zero-probability pairs allowed
--   - encoding: h : Y × Δ_k → ℝ̄, judged by its extension by −∞ off Δ_k (Definition 2.2) → h : Fin k → ℝᵏ → EReal with h y z = ⊥ for z ∉ Δ_k; reason: the extension prescribed by Definition 2.2; same functions on Δ_k
--   - encoding: convex–concave conjugates (Definition 2.6: closed proper convex g, closed proper concave h, conjugacy formulas) → IsConvConcConj: the two conjugacy formulas plus properness of g and h; reason: closedness and (con)vexity follow from the formulas (suprema/infima of affine functions); equivalent predicates
--   - encoding: E[v(x, y)] for an ℝ̄-valued v → ∑ₓ ∑_y D x y · v x y in EReal, with 0 · (±∞) = 0; reason: pairs of probability zero do not contribute, as in the paper's treatment of D-null pairs (footnotes 17, 18)
--   - encoding: ‖λ‖₁ → ∑ i, |λ i|; reason: Mathlib's norm on ι → ℝ is the sup norm; this is the ℓ₁ norm
--   - encoding: inf … = max … → IsGreatest of the set of values of feasible z at the EReal infimum of the real objective; reason: equality with a maximum means the supremum equals the infimum and is attained
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), proof of Theorem 1.9, display after 'applying Theorem 3.3 to g1, h1, R, S yields', p.22 (PDF p.24)

import Mathlib
import Definitions.Def_MaskingHardness_IsConvConcConj
import Definitions.Def_MaskingHardness_IsDist
import Definitions.Def_MaskingHardness_lossObjective

namespace MaskingHardness

/-- **Proof of Theorem 1.9, the `z`-form** (Gopalan–Prabhakaran–Tankala, *Universal Hardness From
Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, proof of Theorem 1.9,
display after "applying Theorem 3.3 to g₁, h₁, R, S yields", printed p.22 = PDF p.24).

For finite `X`, `Y = [k]`, a distribution `D` on `X × Y`, a finite collection `C ⊆ {X → ℝᵏ}`,
convex–concave conjugates `g : Y × ℝᵏ → ℝ`, `h : Y × Δ_k → ℝ̄` and `ε ≥ 0`,
`inf_λ E[g(y, π(c_λ(x)))] + ε‖λ‖₁ = max_{z : X × Y → Δ_k} E[h(y, z(x, y))]` subject to
`|E[⟨c(x), z(x, y) − 1⃗/k⟩]| ≤ ε` for all `c ∈ C`; the maximum is attained.

**Formalization Note** "max" is `IsGreatest` of the set of feasible values, with the infimum
taken in `EReal`; `h` equals `−∞` off `Δ_k`; `C` is an indexed family. -/
theorem theorem_1_9_z_form {X ι : Type*} [Fintype X] [Fintype ι] {k : ℕ}
    (D : X → Fin k → ℝ) (hD : IsDist D) (c : ι → X → Fin k → ℝ)
    (g : Fin k → (Fin k → ℝ) → ℝ) (h : Fin k → (Fin k → ℝ) → EReal)
    (hdom : ∀ y z, z ∉ stdSimplex ℝ (Fin k) → h y z = ⊥)
    (hgh : ∀ y, IsConvConcConj (fun a => ((g y a : ℝ) : EReal)) (h y))
    (ε : ℝ) (hε : 0 ≤ ε) :
    IsGreatest
      {v : EReal | ∃ z : X → Fin k → Fin k → ℝ,
        (∀ x y, z x y ∈ stdSimplex ℝ (Fin k)) ∧
        (∀ i, |∑ x, ∑ y, D x y * (c i x ⬝ᵥ (z x y - fun _ => (k : ℝ)⁻¹))| ≤ ε) ∧
        v = ∑ x, ∑ y, ((D x y : ℝ) : EReal) * h y (z x y)}
      (⨅ lam : ι → ℝ, ((lossObjective D c g ε lam : ℝ) : EReal)) := by sorry

end MaskingHardness
