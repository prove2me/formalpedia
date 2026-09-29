-- Prove2me | Theorems.Thm_ModularForm_exists_coe_eq_slash_of_mem_gamma0_gammaH
-- name    : ModularForm.exists_coe_eq_slash_of_mem_gamma0_gammaH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/46c060d0-7ce6-58fd-80a2-5d56a38a61bf
-- title:
--   Slashing a Γ_H(N)-form by an element of Γ₀(N)
-- statement:
--   Let $N$ be a nonzero natural number and $H$ a subgroup of $(\mathbb{Z}/N)^\times$, and let $\Gamma_H(N)$ denote the subgroup [`CohCarrier.GammaH N H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$, namely the image under the inclusion of $\Gamma_0(N)$ of the preimage of $H$ under the homomorphism $\Gamma_0(N) \to (\mathbb{Z}/N)^\times$ sending a matrix to the reduction of its lower right entry; it is viewed here, via the coercion, as a subgroup of $\mathrm{GL}_2(\mathbb{R})$. Let $k$ be an integer and let $f$ be a modular form of weight $k$ for that subgroup of $\mathrm{GL}_2(\mathbb{R})$, that is, a holomorphic function on the upper half plane, invariant under the weight-$k$ slash action of the subgroup and bounded at its cusps. Let $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(N)$. Then there exists a modular form $F$ of the same weight $k$ and for the same subgroup whose underlying function on the upper half plane is equal to $f \mid_k \gamma$. Thus the assertion is that the slashed function $f \mid_k \gamma$ again carries the structure of a weight-$k$ modular form for $\Gamma_H(N)$.
--
--   This is the statement that $\Gamma_H(N)$ is normal in $\Gamma_0(N)$, so that $\Gamma_0(N)$ acts on weight-$k$ modular forms for $\Gamma_H(N)$ by the slash action; it is what makes the diamond operators $\langle d \rangle f = f \mid_k \sigma_d$ into operators on spaces of forms. It is used in the treatment of the diamond automorphisms of modular curves and in statements about $q$-expansion coefficients of slashed forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_coe_eq_slash_of_mem_gamma0_gammaH.lean

import Mathlib
import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularForm.exists_coe_eq_slash_of_mem_gamma0_gammaH
    (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) {k : ℤ}
    (f : ModularForm (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    ∃ F : ModularForm (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) k,
      (⇑F : UpperHalfPlane → ℂ) = ((⇑f : UpperHalfPlane → ℂ) ∣[k] γ) := by sorry
