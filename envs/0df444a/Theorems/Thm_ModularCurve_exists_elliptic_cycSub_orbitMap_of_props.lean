-- Prove2me | Theorems.Thm_ModularCurve_exists_elliptic_cycSub_orbitMap_of_props
-- name    : ModularCurve.exists_elliptic_cycSub_orbitMap_of_props
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/811921d2-90aa-56b7-ab76-d4434088f061
-- title:
--   Orbit correspondence for cyclic N-subgroups over a given j₀
-- statement:
--   Fix a nonzero natural number $N$ and an element $j_0$ of $\overline{\mathbb{Q}}$, and write $H = \mathrm{HahnSeries}\,\mathbb{Q}\,\overline{\mathbb{Q}}$ for the field of Hahn series with rational exponents. Four hypotheses are assumed. `FullKernelIsRootAt N`: for every elliptic Weierstrass curve $W$ over $H$, every affine point $Q$ of exact additive order $N$ whose full-kernel quotient `W.fullKernelQuotient Q N` has nonzero discriminant, and every `ModularPolynomialData N` (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(N)$ annihilating the pair of $q$-expansions), the $j$-invariant of that quotient is a root of $\Phi$ specialised at $j(W)$. `FullKernelInjAt N`: if $j(W)$ is transcendental over $\mathbb{Q}$ and $Q,Q'$ have exact order $N$ with quotients of nonzero discriminant and equal $j$-invariants, then $\langle Q\rangle = \langle Q'\rangle$. `FullKernelDiscAt N`: over any algebraically closed field in which $2 \neq 0$, such quotients have nonzero discriminant. Finally, equivariance: for each `ModularPolynomialData N`, each element $m$ of the monodromy group of $H$, and all roots $r,r'$ of $\Phi$ specialised at the $j$-invariant of `nearCurve j₀` with $r' = m(r)$, the push-forward `B3.b3Act j₀ m` along `nearTransport j₀ m` sends the subgroup attached to $r$ by `dictN` to that attached to $r'$. The conclusion: there is an elliptic curve $E_0$ over $\overline{\mathbb{Q}}$ with $j(E_0) = j_0$ and a map $f$ from `CycSub E₀ N`, the subgroups of $E_0$'s affine point group of the form $\langle g\rangle$ with $g$ of exact order $N$, to the places $w$ of `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$ (valuation subrings containing $\overline{\mathbb{Q}}$, proper, principal) with $\mathrm{ord}_w(\bar{j} - j_0) > 0$, such that $f(\mathcal H) = f(\mathcal H')$ holds exactly when `SameOrbit E₀` holds, i.e. some variable change $\gamma$ fixing $E_0$ carries a generator of $\mathcal H$ to one of $\mathcal H'$, and such that for every such place $w$, $\mathrm{ord}_w(\bar{j} - j_0)$ equals the number of $\mathcal H$ with $f(\mathcal H) = w$.
--
--   This is the level-$N$ form of the comparison between the fibre of the $\Gamma_0(N)$ moduli problem above $j_0$, described by cyclic subgroups of order $N$ up to automorphisms of $E_0$, and the places of the level-$N$ modular function field at which $\bar{j} - j_0$ has positive order, with the order computing the fibre multiplicity. It is stated conditionally on three properties of the full-kernel (Vélu) quotient and one monodromy-equivariance property, and is the form from which [`ModularCurve.exists_elliptic_cycSub_orbitMap`](thm.html#ModularCurve.exists_elliptic_cycSub_orbitMap) is obtained once those inputs are discharged.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_elliptic_cycSub_orbitMap_of_props.lean

import Definitions.Def_ModularCurve_EMD
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_CycSubRootBridgeN
import Definitions.Def_ModularCurve_SpecialisationBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Classical

open ModularCurve ModularCurve.TatePoint AlgebraicCurve

theorem ModularCurve.exists_elliptic_cycSub_orbitMap_of_props (N : ℕ) [NeZero N]
    (j₀ : AlgebraicClosure ℚ)
    (hW1 : FullKernelIsRootAt N) (hW2 : FullKernelInjAt N) (hW3 : FullKernelDiscAt N)
    (hequivN : ∀ data : ModularPolynomialData N,
      ∀ (m : HahnSeries.monodromy Qbar) (r r' : RootsAt data (nearCurve j₀).j),
        r'.1 = (m : H ≃ₐ[Qbar] H) r.1 →
        B3.b3Act j₀ m (dictN N data j₀ hW1 hW2 hW3 r).1 = (dictN N data j₀ hW1 hW2 hW3 r').1)
    :
    ∃ (E₀ : WeierstrassCurve (AlgebraicClosure ℚ)) (_ : E₀.IsElliptic), E₀.j = j₀ ∧
      ∃ f : CycSub E₀ N →
          {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) //
            0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)},
        (∀ H H' : CycSub E₀ N, f H = f H' ↔ SameOrbit E₀ H.1 H'.1) ∧
        ∀ w : {w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) //
            0 < w.ord (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)},
          ((w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).ord
              (jBar N - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) j₀)).toNat =
            Nat.card {H : CycSub E₀ N // f H = w} := by sorry
