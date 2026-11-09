-- Prove2me | Theorems.Thm_MaskingHardness_lemma_A_1
-- name    : MaskingHardness.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:50:47.337903+00:00
-- url     : https://prove2.me/theorems/9f9f3109-86d5-4fec-939b-203c8da5ea93
-- title:
--   Lemma A.1 — $g(y,\pi(a))$ and the shifted fidelity $h_1$ are convex–concave conjugates
-- statement:
--   Let $g:[k]\times\mathbb R^k\to\mathbb R$ and $h:[k]\times\Delta_k\to\overline{\mathbb R}$ be convex–concave conjugates (Definition 2.7, with $h$ extended by $-\infty$ outside the simplex $\Delta_k$). Define
--
--   $$
--   g_1(y,a)=g(y,\pi(a)),\qquad h_1(y,b)=\begin{cases}h(y,z) & \text{if } b=z-\vec 1/k \text{ for some } z\in\Delta_k,\\ -\infty & \text{otherwise,}\end{cases}
--   $$
--
--   where $\pi(a)=a-\langle a,\vec 1/k\rangle\vec 1$ is the centering map. Then $g_1$ and $h_1$ are also convex–concave conjugates.
--
--   The lemma moves the problem of the main theorem from the simplex to the mean-zero hyperplane so that the six-functions theorem applies.
--
--   **Formalization Note** $h$ is a function on $\mathbb R^k$ that equals $-\infty$ off $\Delta_k$; the conclusion is stated for every label $y$.
--
--   Differences from the source:
--   - generalization: h : Y × Δ_k → ℝ (real-valued on the simplex) → h : Fin k → ℝᵏ → EReal, allowed to be −∞ on parts of Δ_k; reason: Theorem 1.9 applies the lemma to ℝ̄-valued fidelity functions (Example 1.7, log zᵢ); a real-valued h is the special case
--   - encoding: h : Y × Δ_k → ℝ̄, judged by its extension by −∞ off Δ_k (Definition 2.2) → h : Fin k → ℝᵏ → EReal with h y z = ⊥ for z ∉ Δ_k; reason: the extension prescribed by Definition 2.2; same functions on Δ_k
--   - encoding: convex–concave conjugates (Definition 2.6: closed proper convex g, closed proper concave h, conjugacy formulas) → IsConvConcConj: the two conjugacy formulas plus properness of g and h; reason: closedness and (con)vexity follow from the formulas (suprema/infima of affine functions); equivalent predicates
--   - encoding: Y = [k]; ⃗1/k; h₁ defined via 'b = z − ⃗1/k for some z ∈ Δ_k' → Fin k; the constant vector (k : ℝ)⁻¹; shiftH tests b + ⃗1/k ∈ Δ_k; reason: the only candidate z is b + ⃗1/k; same function
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Lemma A.1, p.39 (PDF p.41)

import Mathlib
import Definitions.Def_MaskingHardness_IsConvConcConj
import Definitions.Def_MaskingHardness_centered
import Definitions.Def_MaskingHardness_shiftH

namespace MaskingHardness

/-- **Lemma A.1** (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*,
arXiv:2611.05296, held version sha256 31134e8d…3e8d, Lemma A.1, printed p.39 = PDF p.41).

Given convex–concave conjugates `g : Y × ℝᵏ → ℝ` and `h : Y × Δ_k → ℝ̄`, define
`g₁(y, a) = g(y, π(a))` and `h₁(y, b) = h(y, z)` if `b = z − 1⃗/k` for some `z ∈ Δ_k`, `−∞`
otherwise. Then `g₁, h₁` are convex–concave conjugates.

**Formalization Note** `Y = [k]` is `Fin k`; `h` is given on all of `ℝᵏ` and equals `−∞` off
`Δ_k` (the extension of Definition 2.2); the paper prints `h : Y × Δ_k → ℝ`, and the statement
here allows `h` to take the value `−∞` on `Δ_k` as well. -/
theorem lemma_A_1 {k : ℕ} (g : Fin k → (Fin k → ℝ) → ℝ) (h : Fin k → (Fin k → ℝ) → EReal)
    (hdom : ∀ y z, z ∉ stdSimplex ℝ (Fin k) → h y z = ⊥)
    (hgh : ∀ y, IsConvConcConj (fun a => ((g y a : ℝ) : EReal)) (h y)) :
    ∀ y, IsConvConcConj (fun a => ((g y (centered a) : ℝ) : EReal)) (shiftH h y) := by sorry

end MaskingHardness
