-- Prove2me | Theorems.Thm_ModularCurve_SSHeckeV2_exists_isModPEigen_modPCusp_of_eigen_riemannRochSpace
-- name    : ModularCurve.SSHeckeV2.exists_isModPEigen_modPCusp_of_eigen_riemannRochSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/8cce3457-2281-5843-9497-082762ba7ce9
-- title:
--   Cuspidal Hecke eigen-function yields mod-p cusp eigenform of weight 2m'
-- statement:
--   Let $p \ge 5$ be a prime, $K$ an algebraically closed field of characteristic $p$, and $N \ge 1$ with $N \ne 0$ in $K$; let $S_0 \subseteq \mathbb{N}$ be a set of naturals containing $p$, let $m' \ge 1$, and let $\lambda : \mathbb{N} \to K$. Let $G$ be a nonzero element of $\mathrm{modularFunctionFieldC}\,K\,N = K(j_q, j_{q,N})$ inside the Laurent series field $\mathrm{LaurentSeries}\,K$, assumed to lie in the Riemann–Roch space of the divisor $\mathrm{weightDivisor}\,K\,N\,m'$, i.e. $v(G) \le \exp(D v)$ for every place $v$ of this field over $K$, and assumed to satisfy $\mathrm{IsModPCuspFormFn}\,K\,m'$: the element $G^6 j^{4m'} (j-1728)^{3m'}$ is integral over $K[j]$ and, for some $M$, $G^{2M} j^{m'M+1} (j-1728)^{m'M}$ is integral over $K[j^{-1}]$, where $j = \mathrm{jqModC}\,K$. Suppose further that for every prime $\ell$ with $\ell \nmid N$ and $\ell \notin S_0$ one has $\ell^{m'-1} \cdot \mathrm{Tr}\big(\beta_\ell(G)\, \epsilon_\ell^{m'}\big) = \lambda(\ell)\, G$, the trace being taken from the degeneracy roof $K(j_q, j_{q,N}, j_{q,\ell}, j_{q,N\ell})$ to the modular function field along $\mathrm{heckeAlphaC}$, with $\beta_\ell = \mathrm{heckeBetaC}\,K\,N\,\ell$ and $\epsilon_\ell = \mathrm{heckeMultiplier}\,N\,K\,\ell$ the multiplier comparing $D(\beta_\ell(\mathrm{jGeomGen}))$ with the image of $D(\mathrm{jGeomGen})$. Then there exists a power series $\psi$ over $K$ whose image in $\mathrm{LaurentSeries}\,K$ equals $G \cdot (\theta\, j)^{m'}$, where $\theta f = q\,df/dq$, such that $\psi$ lies in $\mathrm{ModPForms.modPCusp}\,N\,(2m')\,K$, the $K$-span of mod-$p$ reductions of integral $q$-expansions of weight-$2m'$ cusp forms on $\Gamma_0(N)$, and $\psi$ is a mod-$p$ eigenform in the sense of $\mathrm{IsModPEigen}$: $\psi \ne 0$ and $T_\ell \psi = \lambda(\ell)\,\psi$ for all primes $\ell \nmid N$ with $\ell \notin S_0$.
--
--   This is the cuspidal counterpart of the passage from a Hecke eigen-function in a Riemann–Roch space on the modular curve in characteristic $p$ to a mod-$p$ modular form: the geometric eigenvector $G$, multiplied by $(\theta j)^{m'}$, is recognised as the $q$-expansion of a mod-$p$ cusp form of weight $2m'$ with the same eigenvalue system $\lambda$ away from $N$ and $S_0$. It is used by [`ModularCurve.SSHeckeV2.ssHeckeFun_window`](thm.html#ModularCurve.SSHeckeV2.ssHeckeFun_window), where cuspidal weight data are produced on the dual side of the construction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SSHeckeV2_exists_isModPEigen_modPCusp_of_eigen_riemannRochSpace.lean

import Mathlib
import Definitions.Def_ModularCurve_SSHeckeV2
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_WeightDivisor
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve ModularCurve

theorem ModularCurve.SSHeckeV2.exists_isModPEigen_modPCusp_of_eigen_riemannRochSpace (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (S₀ : Set ℕ) (hS₀p : p ∈ S₀)
    (m' : ℕ) (hm' : 1 ≤ m') (G : ↥(modularFunctionFieldC K N)) (hG0 : G ≠ 0)
    (hG : G ∈ AlgebraicCurve.riemannRochSpace (ModularCurve.weightDivisor K N m'))
    (hcusp : ModularCurve.IsModPCuspFormFn K m' (G : LaurentSeries K)) (lam : ℕ → K)
    (heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
      haveI : Fact ℓ.Prime := ⟨hℓ⟩
      letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
      algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ (m' - 1)) *
          Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
            (heckeBetaC K N ℓ G * ModularCurve.heckeMultiplier N K ℓ ^ m')
        = algebraMap K ↥(modularFunctionFieldC K N) (lam ℓ) * G) :
    ∃ ψ : PowerSeries K,
      HahnSeries.ofPowerSeries ℤ K ψ = (G : LaurentSeries K) * thetaL K (jqModC K) ^ m' ∧
      ψ ∈ ModPForms.modPCusp N (2 * (m' : ℤ)) K ∧ ModPForms.IsModPEigen N S₀ (2 * (m' : ℤ)) ψ lam := by sorry
