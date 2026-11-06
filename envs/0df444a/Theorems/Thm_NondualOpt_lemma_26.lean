-- Prove2me | Theorems.Thm_NondualOpt_lemma_26
-- name    : NondualOpt.lemma_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T23:59:32.051947+00:00
-- url     : https://prove2.me/theorems/e76107f4-305b-4f94-89fd-a7fc799ea7db
-- title:
--   Lemma 26 — uniformly convex localization
-- statement:
--   Let $(E,\|\cdot\|)$ be a real normed space and suppose $\|g\|_*\le L$ for every $g\in H$. Let $K\subseteq E$ be convex and let $\Phi$ be $(c,\kappa)$-uniformly convex on $K$ ($c>0$, $\kappa\ge2$) with range $\sup_K\Phi-\inf_K\Phi\le D$. Then for every $\alpha>0$
--   $$
--   \mathrm{sfat}_\alpha(L_{K,H})\le\frac Dc\Big(\frac L\alpha\Big)^\kappa .
--   $$
--   In particular the dimension is finite. Applied to $\ell_r$ balls, for which uniformly convex potentials are classical, it bounds the local classes of Proposition 28.
--
--   Differences from the source:
--   - generalization: H ⊆ E∗ with ‖g‖_∗ ≤ L → H in a real vector space F paired bilinearly with E, |⟨g, u⟩| ≤ L‖u‖ for all u ∈ E; reason: for F = E∗ this is the dual-norm bound; the class L_{K,H} depends on H only through the pairing
--   - generalization: range_K(Φ) = D → any D with Φ(u) − Φ(v) ≤ D on K; reason: specializes to D = range_K(Φ)
--   - encoding: Φ : K → ℝ → Φ : E → ℝ; reason: only the values on K enter
--   - encoding: the scale α → α > 0; reason: Definition 1 takes α > 0
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Lemma 26, p.38; Definition 25, p.37

import Mathlib
import Definitions.Def_NondualOpt_IsUnifConvexOn
import Definitions.Def_NondualOpt_linClass
import Definitions.Def_NondualOpt_sfat

open scoped ENNReal

namespace NondualOpt

/-- **Lemma 26 (Uniformly convex localization).** Let `(E, ‖·‖)` be a real normed space with
`‖g‖_∗ ≤ L` for every `g ∈ H`, `K ⊆ E` convex, and `Φ` `(c, κ)`-uniformly convex on `K` with range
`D`. Then `sfat_α(L_{K,H}) ≤ (D/c)(L/α)^κ`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Lemma 26, p.38 (Definition 25, p.37).

**Formalization Note.** (i) `H` lies in a real vector space `F` paired bilinearly with `E`, and
`‖g‖_∗ ≤ L` is `|⟨g, u⟩| ≤ L‖u‖` for all `u ∈ E` (for `F = E∗` this is the dual-norm bound).
(ii) `D` is any upper bound on the range `sup_K Φ − inf_K Φ`. (iii) `c > 0`, `κ ≥ 2`
(Definition 25) and `α > 0` (Definition 1). The bound asserts finiteness of `sfat`. -/
theorem lemma_26 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [AddCommGroup F]
    [Module ℝ F] (pair : F →ₗ[ℝ] E →ₗ[ℝ] ℝ) (H : Set F) (L : ℝ)
    (hL : ∀ g ∈ H, ∀ u, |pair g u| ≤ L * ‖u‖) (K : Set E) (hK : Convex ℝ K) (Φ : E → ℝ)
    (c κ D : ℝ) (hc : 0 < c) (hκ : 2 ≤ κ) (hΦ : IsUnifConvexOn K Φ c κ)
    (hD : ∀ u ∈ K, ∀ v ∈ K, Φ u - Φ v ≤ D) (α : ℝ) (hα : 0 < α) :
    (sfat (linClass pair K H) α : ℝ≥0∞) ≤ ENNReal.ofReal (D / c * (L / α) ^ κ) := by sorry

end NondualOpt
