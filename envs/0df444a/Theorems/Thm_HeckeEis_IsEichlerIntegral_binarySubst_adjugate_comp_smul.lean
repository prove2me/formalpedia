-- Prove2me | Theorems.Thm_HeckeEis_IsEichlerIntegral_binarySubst_adjugate_comp_smul
-- name    : HeckeEis.IsEichlerIntegral.binarySubst_adjugate_comp_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/7d13aadd-a481-5cb5-934a-fe21684123f3
-- title:
--   Eichler integrals under integral matrices of positive determinant
-- statement:
--   Fix $n \in \mathbb{N}$, a function $f : \mathbb{H} \to \mathbb{C}$ and a function $F$ from $\mathbb{H}$ to the submodule [`HeckeEis.BinaryForm ℂ n`](def/HeckeEis_BinaryFormRep.html#L25) of degree-$n$ homogeneous polynomials in $\mathbb{C}[X_0,X_1]$, and suppose [`HeckeEis.IsEichlerIntegral n f F`](def/HeckeEis_EichlerIntegral.html#L105) holds, i.e. for every multidegree $d : \mathrm{Fin}\,2 \to_{0} \mathbb{N}$ and every $\tau \in \mathbb{H}$ the function $z \mapsto \operatorname{coeff}_d F(\mathrm{ofComplex}\,z)$ has derivative $f(\tau)\cdot \operatorname{coeff}_d\big((\tau X_0 + X_1)^n\big)$ at $z = \tau$. Let $M$ be a $2\times 2$ integer matrix with $\det M > 0$, and let $\beta \in \mathrm{GL}_2(\mathbb{R})$ have underlying real matrix the entrywise image of $M$ under $\mathbb{Z} \to \mathbb{R}$. The conclusion is that [`HeckeEis.IsEichlerIntegral n`](def/HeckeEis_EichlerIntegral.html#L105) again holds for the pair consisting of the weight-$(n+2)$ slash $f \mid[(n:\mathbb{Z})+2]\,\beta$, given by $\tau \mapsto (\det\beta)^{n+1} j(\beta,\tau)^{-(n+2)} f(\beta\cdot\tau)$, and of the function $\tau \mapsto \mathrm{adj}(M)\cdot F(\beta\cdot\tau)$, where $\mathrm{adj}(M)$ acts through [`HeckeEis.binarySubst ℂ M.adjugate`](def/HeckeEis_BinaryFormRep.html#L28), the algebra endomorphism of $\mathbb{C}[X_0,X_1]$ sending $X_j$ to $\sum_i \mathrm{adj}(M)_{ij} X_i$, restricted to degree-$n$ forms via [`HeckeEis.binarySubst_mem`](def/HeckeEis_BinaryFormRep.html#L52).
--
--   This is the Hecke-equivariance step for Eichler integrals: an Eichler integral of $f$ in weight $n+2$ transforms, under an integral matrix of positive determinant, into an Eichler integral of the slashed form, with the binary-form values twisted by the adjugate substitution. It is used in the computation of the action of the Hecke operators $T_\ell$ and $U_\ell$ on Eichler–Shimura cohomology classes, in [`HeckeEis.coeffH1Mk_cocycle_heckeTLin_modularForm`](thm.html#HeckeEis.coeffH1Mk_cocycle_heckeTLin_modularForm), [`HeckeEis.eichlerShimuraMap_heckeTLin`](thm.html#HeckeEis.eichlerShimuraMap_heckeTLin) and [`HeckeEis.eichlerShimuraMap_heckeULin`](thm.html#HeckeEis.eichlerShimuraMap_heckeULin).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_IsEichlerIntegral_binarySubst_adjugate_comp_smul.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

theorem HeckeEis.IsEichlerIntegral.binarySubst_adjugate_comp_smul {n : ℕ} {f : UpperHalfPlane → ℂ}
    {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)} (hF : HeckeEis.IsEichlerIntegral n f F)
    {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : 0 < M.det) {β : GL (Fin 2) ℝ}
    (hβM : (β : Matrix (Fin 2) (Fin 2) ℝ) = M.map (algebraMap ℤ ℝ)) :
    HeckeEis.IsEichlerIntegral n (f ∣[((n : ℤ) + 2)] β)
      (fun τ => ((HeckeEis.binarySubst ℂ M.adjugate).toLinearMap.restrict
        (fun _ h => HeckeEis.binarySubst_mem ℂ M.adjugate h)) (F (β • τ))) := by sorry
