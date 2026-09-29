-- Prove2me | Theorems.Thm_ModularCurve_periodMap_rescaleLin_apply
-- name    : ModularCurve.periodMap_rescaleLin_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/9fc98e7e-5371-5fb0-818b-6072e62321d3
-- title:
--   Period map commutes with the degeneracy map V_d
-- statement:
--   Let $R$, $M$, $d$ be nonzero natural numbers with $dR \mid M$, and let $h$ witness [`CohCarrier.LevelLE R M ⊤ ⊤ d`](def/CohCarrier_Level.html#L330), i.e. $R \mid M$, $d \mid M/R$ and the (vacuous, for the full unit subgroups) condition that reduction modulo $R$ carries $\top \le (\mathbb{Z}/M)^\times$ into $\top \le (\mathbb{Z}/R)^\times$. Let $f$ be a weight-$2$ cusp form for $\Gamma_0(R)$ and let $\gamma$ lie in [`CohCarrier.GammaH M ⊤`](def/CohCarrier_Level.html#L133), the image in $\mathrm{SL}(2,\mathbb{Z})$ of $\Gamma_0(M)$ (the preimage of $\top$ under the character $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$). Write $V_d f =$ [`FreyPackage.ModMCarrier.rescaleLin hdRM 2 f`](def/FreyPackage_ModMCarrier_Rescale.html#L140) for the weight-$2$ cusp form on $\Gamma_0(M)$ whose underlying function is $f \mid_2 \mathrm{diag}(d,1)$. Then the value of [`ModularCurve.periodMap M`](def/ModularCurve_PeriodMapBundled.html#L20) applied to $V_d f$ at the additive generator attached to $\gamma$, viewed in $\Gamma_0(M)$, equals the value of [`ModularCurve.periodMap R`](def/ModularCurve_PeriodMapBundled.html#L20) applied to $f$ at the additive generator attached to [`CohCarrier.iotaDeg R M ⊤ ⊤ d h γ`](def/CohCarrier_Level.html#L383), viewed in $\Gamma_0(R)$; the latter element is $\bigl(\begin{smallmatrix} a & bd \\ c/d & e\end{smallmatrix}\bigr)$ for $\gamma = \bigl(\begin{smallmatrix} a & b \\ c & e\end{smallmatrix}\bigr)$, that is $\mathrm{diag}(d,1)\,\gamma\,\mathrm{diag}(d,1)^{-1}$.
--
--   This is the compatibility of the Eichler–Shimura period characters with the degeneracy (oldform) map $V_d : S_2(\Gamma_0(R)) \to S_2(\Gamma_0(M))$, $V_d f = f\mid_2 \mathrm{diag}(d,1)$: periods of $V_d f$ along $\gamma \in \Gamma_0(M)$ are periods of $f$ along the conjugate $\mathrm{diag}(d,1)\gamma\,\mathrm{diag}(d,1)^{-1} \in \Gamma_0(R)$. It is used in the analysis of parabolic homomorphisms attached to the degeneracy maps, namely by [`CohCarrier.eq_zero_of_iDegL_one_add_iDegL_eq_zero_of_mem_parabolicHoms`](thm.html#CohCarrier.eq_zero_of_iDegL_one_add_iDegL_eq_zero_of_mem_parabolicHoms) and [`CohCarrier.exists_eq_iDegL_one_add_iDegL_of_mem_parabolicHoms_of_heckeT_eq_smul`](thm.html#CohCarrier.exists_eq_iDegL_one_add_iDegL_of_mem_parabolicHoms_of_heckeT_eq_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_periodMap_rescaleLin_apply.lean

import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMapBundled
import Definitions.Def_FreyPackage_ModMCarrier_Rescale

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.periodMap_rescaleLin_apply
    {R M d : ℕ} [NeZero R] [NeZero M] [NeZero d] (hdRM : d * R ∣ M)
    (h : CohCarrier.LevelLE R M ⊤ ⊤ d)
    (f : CuspForm (CongruenceSubgroup.Gamma0 R) 2) (γ : ↥(CohCarrier.GammaH M ⊤)) :
    ModularCurve.periodMap M (FreyPackage.ModMCarrier.rescaleLin hdRM 2 f)
        (Additive.ofMul ⟨(γ : SL(2, ℤ)), CohCarrier.GammaH_le_Gamma0 ⊤ γ.2⟩) =
      ModularCurve.periodMap R f
        (Additive.ofMul ⟨(CohCarrier.iotaDeg R M ⊤ ⊤ d h γ : SL(2, ℤ)),
          CohCarrier.GammaH_le_Gamma0 ⊤ (CohCarrier.iotaDeg R M ⊤ ⊤ d h γ).2⟩) := by sorry
