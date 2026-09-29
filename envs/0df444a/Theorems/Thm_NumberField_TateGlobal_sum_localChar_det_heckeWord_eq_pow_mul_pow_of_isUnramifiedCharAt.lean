-- Prove2me | Theorems.Thm_NumberField_TateGlobal_sum_localChar_det_heckeWord_eq_pow_mul_pow_of_isUnramifiedCharAt
-- name    : NumberField.TateGlobal.sum_localChar_det_heckeWord_eq_pow_mul_pow_of_isUnramifiedCharAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/dbd293d9-92d6-5492-99ac-d4a5f3f61fc9
-- title:
--   Unramified χ∘det on Hecke words over GL₂(Kᵥ)
-- statement:
--   Let $K$ be a number field, $v$ a nonzero prime of $\mathcal O_K$ with completion $K_v$ and valuation ring $\mathcal O_v$, and let $\chi$ be a homomorphism from the ideles $(\mathbb A_K)^\times$ to $\mathbb C^\times$. Assume $\chi$ is unramified at $v$ in the sense that for every unit $t$ of $K_v$ with both $t$ and $t^{-1}$ in $\mathcal O_v$ one has $\chi(\iota_v(t))=1$, where $\iota_v(t)$ is the idele equal to $t$ at $v$ and to $1$ at all other places. Let $\varpi\in\mathcal O_v$ be irreducible with nonzero image in $K_v$, let $U\le \mathrm{GL}_2(K_v)$ be the image of $\mathrm{GL}_2(\mathcal O_v)$, and let $r_0,\dots,r_{n-1}\in\mathrm{GL}_2(K_v)$ be a Hecke coset system for $U$ and $g=\mathrm{diag}(\varpi,1)$: each $r_i$ lies in $UgU$, every element of $UgU$ lies in some coset $r_iU$, and the cosets $r_iU$ are pairwise distinct. Let $z\in\mathrm{GL}_2(K_v)$ have underlying matrix the scalar $\varpi\cdot 1$, and let $k,j\in\mathbb N$. Then $$\sum_{\iota\colon \mathrm{Fin}\,k\to\mathrm{Fin}\,n}\chi_v\bigl(\det(r_{\iota(0)}\cdots r_{\iota(k-1)}\,z^{\,j})\bigr)=\bigl((N(v)+1)\,\chi(\hat\varpi_v)\bigr)^k\bigl(\chi(\hat\varpi_v)^2\bigr)^j$$ as complex numbers, where $\chi_v=\chi\circ\iota_v$, $N(v)$ is the absolute norm of the prime ideal of $v$, and $\hat\varpi_v$ is the idele given by the distinguished uniformizer of $K_v$ at $v$ and $1$ elsewhere.
--
--   This is the computation of the eigenvalue of the unramified local Hecke operator at $v$, and of the central element, on the one-dimensional representation $\chi_v\circ\det$ of $\mathrm{GL}_2(K_v)$, summed over all words of length $k$ in a system of coset representatives for the double coset of $\mathrm{diag}(\varpi,1)$. It is used in the limit statement on twisted convolution operators attached to $\chi\circ\det$, [`AutomorphicForm.exists_atomic_forall_integrableOn_and_tendsto_setIntegral_lambdaT_finsum_twistedConvOp_chiDet_mul_chiDet_inv`](thm.html#AutomorphicForm.exists_atomic_forall_integrableOn_and_tendsto_setIntegral_lambdaT_finsum_twistedConvOp_chiDet_mul_chiDet_inv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_sum_localChar_det_heckeWord_eq_pow_mul_pow_of_isUnramifiedCharAt.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_HeckeEigenfunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.TateGlobal.sum_localChar_det_heckeWord_eq_pow_mul_pow_of_isUnramifiedCharAt
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχ : NumberField.TateGlobal.IsUnramifiedCharAt χ v)
    (ϖ : v.adicCompletionIntegers K) (hirr : Irreducible ϖ)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (n : ℕ) (r : Fin n → GL (Fin 2) (v.adicCompletion K))
    (hr : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
      (LocalGL2.diagPi ϖ hϖ0) r)
    (z : GL (Fin 2) (v.adicCompletion K))
    (hz : (z : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (k j : ℕ) :
    ∑ ι : Fin k → Fin n,
        ((NumberField.TateGlobal.localChar χ v
          (Matrix.GeneralLinearGroup.det ((List.ofFn fun m => r (ι m)).prod * z ^ j)) : ℂˣ) : ℂ) =
      ((((Ideal.absNorm v.asIdeal : ℕ) : ℂ) + 1) *
          ((χ (AutomorphicForm.uniformizerIdele K v) : ℂˣ) : ℂ)) ^ k *
        (((χ (AutomorphicForm.uniformizerIdele K v) : ℂˣ) : ℂ) ^ 2) ^ j := by sorry
