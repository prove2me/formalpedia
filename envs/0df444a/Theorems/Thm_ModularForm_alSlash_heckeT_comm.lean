-- Prove2me | Theorems.Thm_ModularForm_alSlash_heckeT_comm
-- name    : ModularForm.alSlash_heckeT_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/a9e50404-b7d6-57d4-a1cd-aa46678468d6
-- title:
--   Atkin–Lehner operator commutes with T_ℓ, ℓ∤ M
-- statement:
--   Let $M$ be a non-zero natural number and $q$ a natural number, and let $W$ be an Atkin–Lehner datum for the pair $(M,q)$, that is, data consisting of a natural number $R$ with $M = qR$ together with integers $a,b$ satisfying $qa - Rb = 1$; attached to such a datum is the element [`ModularForm.AtkinLehnerDatum.alGL`](def/ModularForm_AtkinLehnerDatum.html#L93) of $\mathrm{GL}_2(\mathbb{R})$, the image of an integral matrix `W.mat` of determinant $q$ under $\mathbb{Z}\to\mathbb{R}$, invertible since $q\neq 0$. Let $k$ be an integer, let $\ell$ be a prime not dividing $M$, and let $f : \mathbb{H}\to\mathbb{C}$ be any function (no holomorphy or growth condition is imposed) which is invariant under the weight-$k$ slash action of $\Gamma_0(M)$, viewed as a subgroup of $\mathrm{GL}_2(\mathbb{R})$: $f\mid_k\gamma = f$ for every $\gamma\in\Gamma_0(M)$. Write $T_\ell$ for the operator [`ModularForm.heckeT k ℓ`](def/ModularForm_HeckeOperator.html#L96), sending $g$ to $\sum_{j=0}^{\ell-1} g\mid_k (\mathtt{heckeMatrix}\ \ell\ j) + g\mid_k \mathrm{diag}(\ell,1)$. Then the two functions $\mathbb{H}\to\mathbb{C}$ obtained by slashing $T_\ell f$ by `W.alGL` and by applying $T_\ell$ to $f\mid_k$`W.alGL` coincide: $(T_\ell f)\mid_k W = T_\ell(f\mid_k W)$.
--
--   This is the classical commutation of the Atkin–Lehner operator $w_q$ with the Hecke operator $T_\ell$ at primes $\ell$ prime to the level, here in the form of an identity of functions on the upper half-plane for $\Gamma_0(M)$-invariant functions. It is used in the treatment of newforms and of normalised eigenforms, transporting a $T_\ell$-eigenvalue from $f$ to its Atkin–Lehner transform, and is cited by the results on new subspaces and eigenform existence for cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_alSlash_heckeT_comm.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_AtkinLehnerDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.alSlash_heckeT_comm {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    {f : UpperHalfPlane → ℂ} (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)), SlashAction.map k γ f = f) :
    ModularForm.alSlash W k (ModularForm.heckeT k ℓ f) = ModularForm.heckeT k ℓ (ModularForm.alSlash W k f) := by sorry
