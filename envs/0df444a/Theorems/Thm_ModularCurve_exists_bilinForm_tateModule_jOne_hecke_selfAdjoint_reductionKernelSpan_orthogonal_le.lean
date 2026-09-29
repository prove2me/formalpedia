-- Prove2me | Theorems.Thm_ModularCurve_exists_bilinForm_tateModule_jOne_hecke_selfAdjoint_reductionKernelSpan_orthogonal_le
-- name    : ModularCurve.exists_bilinForm_tateModule_jOne_hecke_selfAdjoint_reductionKernelSpan_orthogonal_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/afa13564-bd05-5c21-bcba-b219ff00546d
-- title:
--   Hecke-self-adjoint perfect pairing on the Tate module of J₁(M)
-- statement:
--   Let $M\ge 1$, let $p$ be a prime not dividing $M$, and let $K$ be a field of characteristic zero equipped with a $\mathbb{Z}_p$-algebra structure. Write $J_1(M)$ for [`ModularCurve.JOne M`](def/ModularCurve_X1.html#L186), the degree-zero divisor class group $\mathrm{Pic}^0$ of the base change to $\overline{\mathbb{Q}}$ of the $q$-expansion function field of $X_1(M)$, carrying the module structure [`ModularCurve.heckeModuleOneBar M`](def/ModularCurve_X1HeckeModule.html#L129) over [`ModularCurve.HeckeAlgOne`](def/ModularCurve_X1HeckeModule.html#L16) $=\mathbb{Z}[X_i]$ with indeterminates indexed by $\mathrm{Primes}\sqcup\mathbb{N}$ (given by the Hecke and diamond evaluation when the commutation condition `HeckeDiamondCommuteBar M` holds, and otherwise by evaluation of polynomials at $0$). Let $T=$ [`TateModule p (JOne M)`](def/EllipticCurve_TateModule.html#L15) be the group of sequences $x:\mathbb{N}\to J_1(M)$ with $p^n x_n=0$ and $p\,x_{n+1}=x_n$ for all $n$. Then for every valuation subring $P$ of $\overline{\mathbb{Q}}$ with the image of $p$ a non-unit of $P$ there is a $K$-bilinear form $B$ on $K\otimes_{\mathbb{Z}_p}T$ such that: $B$ is nondegenerate on both sides; for every $t\in$ `HeckeAlgOne` the base change to $K$ of the levelwise action of $t$ on $T$ is self-adjoint for $B$; and the $K$-span $S$ of the image of $\{x\in T:\ \mathrm{red}_P(x_n)=0\ \text{for all } n\}$ under $x\mapsto 1\otimes x$ satisfies $S^{\perp}\subseteq S$, where $\mathrm{red}_P$ is `reductionQExpModL P (Gamma1 M)`, the reduction map on $\mathrm{Pic}^0$ along the residue map of $P$.
--
--   Classically the form $B$ is the $K$-linear extension of the $p$-adic Weil pairing on the Tate module of the principally polarised Jacobian $J_1(M)$, twisted by the Fricke involution so that all Hecke and diamond operators become self-adjoint, the last clause expressing that the span of the kernel of reduction at $P$ contains its own orthogonal complement. It is used in the bound [`ModularCurve.finrank_map_reductionKernelSpan_tateModule_jOne_le_one_of_isUnit`](thm.html#ModularCurve.finrank_map_reductionKernelSpan_tateModule_jOne_le_one_of_isUnit) on the rank of the image of that span.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_bilinForm_tateModule_jOne_hecke_selfAdjoint_reductionKernelSpan_orthogonal_le.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct

theorem ModularCurve.exists_bilinForm_tateModule_jOne_hecke_selfAdjoint_reductionKernelSpan_orthogonal_le
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : ¬ p ∣ M)
    (K : Type) [Field K] [CharZero K] [Algebra ℤ_[p] K] :
    letI := ModularCurve.heckeModuleOneBar M
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∃ B : LinearMap.BilinForm K (K ⊗[ℤ_[p]] TateModule p (ModularCurve.JOne M)),
        (∀ v, (∀ w, B v w = 0) → v = 0) ∧ (∀ w, (∀ v, B v w = 0) → w = 0) ∧
        (∀ (t : ModularCurve.HeckeAlgOne) (v w : K ⊗[ℤ_[p]] TateModule p (ModularCurve.JOne M)),
          B ((ModularCurve.tateHeckeRepOne p (ModularCurve.JOne M) t).baseChange K v) w =
            B v ((ModularCurve.tateHeckeRepOne p (ModularCurve.JOne M) t).baseChange K w)) ∧
        ∀ w : K ⊗[ℤ_[p]] TateModule p (ModularCurve.JOne M),
          (∀ v ∈ Submodule.span K
              ((fun x : TateModule p (ModularCurve.JOne M) => (1 : K) ⊗ₜ[ℤ_[p]] x) ''
                {x | ∀ n : ℕ, ModularCurve.reductionQExpModL P (CongruenceSubgroup.Gamma1 M)
                  ((x : ℕ → ModularCurve.JOne M) n) = 0}), B v w = 0) →
          w ∈ Submodule.span K
              ((fun x : TateModule p (ModularCurve.JOne M) => (1 : K) ⊗ₜ[ℤ_[p]] x) ''
                {x | ∀ n : ℕ, ModularCurve.reductionQExpModL P (CongruenceSubgroup.Gamma1 M)
                  ((x : ℕ → ModularCurve.JOne M) n) = 0}) := by sorry
