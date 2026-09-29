-- Prove2me | Theorems.Thm_ModularForm_alSlash_alSlash
-- name    : ModularForm.alSlash_alSlash
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/8f4dd1a7-7e13-590d-9ff9-9dc2084824cc
-- title:
--   Double Atkin–Lehner slash acts as the scalar q^{k-2}
-- statement:
--   Fix natural numbers $M$ and $q$ with $M \neq 0$, and let $W$ be an Atkin–Lehner datum at $(M,q)$: a natural number $R$ together with a proof that $M = qR$ and integers $a, b$ satisfying $qa - Rb = 1$. Let $k$ be an integer and let $f : \mathbb{H} \to \mathbb{C}$ be a function on the upper half-plane which is invariant under the weight-$k$ slash action of every element of $\Gamma_0(M)$, the latter regarded as a subgroup of $\mathrm{GL}_2(\mathbb{R})$; no holomorphy or growth condition on $f$ is assumed. Write $\mathrm{alSlash}$ for the weight-$k$ slash by `W.alGL`, the element of $\mathrm{GL}_2(\mathbb{R})$ obtained from the integral matrix `W.mat` attached to the datum by mapping its entries into $\mathbb{R}$ (its determinant is nonzero, so this is invertible). The conclusion is that slashing twice by this element returns $f$ scaled by $(q : \mathbb{C})^{k-2}$, that is $\mathrm{alSlash}\,W\,k\,(\mathrm{alSlash}\,W\,k\,f) = q^{\,k-2} \cdot f$, with Mathlib's determinant normalisation of the slash action.
--
--   This is the standard fact that the Atkin–Lehner element at $q$ squares to a scalar on functions invariant under $\Gamma_0(M)$, so that in weight $2$ it induces an involution. It underlies the results on Atkin–Lehner eigenvalues of newforms and on the linear operator induced by $W$ on spaces of cusp forms, in particular the relation $a_q^2 = 1$ for the relevant newforms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_alSlash_alSlash.lean

import Mathlib
import Definitions.Def_ModularForm_AtkinLehnerDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.alSlash_alSlash {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) (k : ℤ) {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)), SlashAction.map k γ f = f) :
    ModularForm.alSlash W k (ModularForm.alSlash W k f) = ((q : ℂ) ^ (k - 2)) • f := by sorry
