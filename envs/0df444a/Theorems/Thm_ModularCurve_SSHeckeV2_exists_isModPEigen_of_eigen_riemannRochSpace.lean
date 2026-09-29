-- Prove2me | Theorems.Thm_ModularCurve_SSHeckeV2_exists_isModPEigen_of_eigen_riemannRochSpace
-- name    : ModularCurve.SSHeckeV2.exists_isModPEigen_of_eigen_riemannRochSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/6dd4b494-c9be-5d23-9224-ce28e6d00907
-- title:
--   Hecke eigenfunctions in L(D_m) give mod-p eigenforms
-- statement:
--   Let $p \ge 5$ be a prime and let $K$ be an algebraically closed field of characteristic $p$; let $N \ge 1$ with $N \ne 0$ in $K$, let $S_0 \subseteq \mathbb{N}$ be a set of naturals containing $p$, and let $m \ge 1$. Let $G$ be a nonzero element of the modular function field `modularFunctionFieldC K N`, the subfield of the Laurent series field $K((q))$ generated over $K$ by the series $j(q)$ and $j(q^N)$, and assume $G$ lies in the Riemann–Roch space of `weightDivisor K N m`, i.e. $v(G) \le \exp(D(v))$ for every place $v$ of that field over $K$, where $D$ is a divisor chosen to take the value `weightFloor K N m` at every place (and $0$ if no such divisor exists). Let $\mathrm{lam} : \mathbb{N} \to K$ and suppose that for every prime $\ell$ with $\ell \nmid N$ and $\ell \notin S_0$, after equipping the degeneracy roof `charLDegeneracyRoof K N ℓ` — the subfield of $K((q))$ generated over $K$ by $j(q), j(q^N), j(q^{\ell}), j(q^{N\ell})$ — with the algebra structure over the modular function field coming from the inclusion `heckeAlphaC K N ℓ`, one has
--   $$\ell^{m-1}\,\operatorname{Tr}\bigl(\beta_\ell(G)\cdot h_\ell^{\,m}\bigr) = \mathrm{lam}(\ell)\cdot G,$$
--   the trace being taken from the roof down to the modular function field, $\beta_\ell$ the map `heckeBetaC K N ℓ`, and $h_\ell$ the multiplier `heckeMultiplier N K ℓ` chosen so that $D(\beta_\ell(\mathrm{jGeomGen}\,K\,N)) = h_\ell \cdot D(\mathrm{jGeomGen}\,K\,N)$ on Kähler differentials over $K$. Then there exists a power series $\psi \in K[[q]]$ whose image in $K((q))$ equals $G \cdot (\theta j)^m$, where $\theta = q\,\mathrm{d}/\mathrm{d}q$ is `thetaL` applied to $j(q)$, such that $\psi$ lies in [`ModPForms.modPMod N (2m) K`](def/CuspForm_ModPForms.html#L12), the $K$-span of coefficientwise reductions of $q$-expansions of classical modular forms of weight $2m$ on $\Gamma_0(N)$ with integral coefficients, and $\psi$ satisfies [`ModPForms.IsModPEigen N S₀ (2m) ψ lam`](def/CuspForm_ModPForms.html#L24): $\psi \ne 0$ and for every prime $\ell \nmid N$ with $\ell \notin S_0$ the formal Hecke operator in weight $2m$, sending $\psi$ to the series with $n$-th coefficient $a_{n\ell}(\psi) + \ell^{2m-1} a_{n/\ell}(\psi)$ (the second term present only when $\ell \mid n$), acts on $\psi$ by the scalar $\mathrm{lam}(\ell)$.
--
--   This is the passage from the geometric side to the $q$-expansion side: a nonzero section of the weight-$2m$ floor divisor on the coarse modular curve in characteristic $p$, eigen for the Hecke correspondences away from $N$ and $S_0$, produces a mod-$p$ modular form of weight $2m$ and level $N$ with the same eigenvalues, the comparison being the multiplication by $(\theta j)^m$ that converts functions into weight-$2m$ $q$-expansions. It is used in the construction of the Hecke eigenform window [`ModularCurve.SSHeckeV2.ssHeckeFun_window`](thm.html#ModularCurve.SSHeckeV2.ssHeckeFun_window).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SSHeckeV2_exists_isModPEigen_of_eigen_riemannRochSpace.lean

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

theorem ModularCurve.SSHeckeV2.exists_isModPEigen_of_eigen_riemannRochSpace (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (S₀ : Set ℕ) (hS₀p : p ∈ S₀)
    (m : ℕ) (hm : 1 ≤ m) (G : ↥(modularFunctionFieldC K N)) (hG0 : G ≠ 0)
    (hG : G ∈ AlgebraicCurve.riemannRochSpace (ModularCurve.weightDivisor K N m)) (lam : ℕ → K)
    (heig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ N → ℓ ∉ S₀ →
      haveI : Fact ℓ.Prime := ⟨hℓ⟩
      letI := AlgebraicCurve.algebraAlong (heckeAlphaC K N ℓ)
      algebraMap K ↥(modularFunctionFieldC K N) ((ℓ : K) ^ (m - 1)) *
          Algebra.trace ↥(modularFunctionFieldC K N) ↥(charLDegeneracyRoof K N ℓ)
            (heckeBetaC K N ℓ G * ModularCurve.heckeMultiplier N K ℓ ^ m)
        = algebraMap K ↥(modularFunctionFieldC K N) (lam ℓ) * G) :
    ∃ ψ : PowerSeries K,
      HahnSeries.ofPowerSeries ℤ K ψ = (G : LaurentSeries K) * thetaL K (jqModC K) ^ m ∧
      ψ ∈ ModPForms.modPMod N (2 * (m : ℤ)) K ∧ ModPForms.IsModPEigen N S₀ (2 * (m : ℤ)) ψ lam := by sorry
