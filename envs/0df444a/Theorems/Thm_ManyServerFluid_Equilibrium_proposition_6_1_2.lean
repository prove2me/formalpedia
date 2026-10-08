-- Prove2me | Theorems.Thm_ManyServerFluid_Equilibrium_proposition_6_1_2
-- name    : ManyServerFluid.Equilibrium.proposition_6_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:57.321924+00:00
-- url     : https://prove2.me/theorems/fa95ddfa-201e-4ec7-b4ab-80fbc7247e28
-- title:
--   Proposition 6.1(2) — constant rate λ̄ ∈ [0, 1] from empty: X̄(t) = ⟨1, ν̄_t⟩ ↑ λ̄ and ν̄_t ↑ λ̄ν̄* weakly
-- statement:
--   Suppose Assumption 2 holds, the arrival rate is a constant $\bar\lambda\in[0,1]$ (so $\bar E(t)=\bar\lambda t$), the system starts empty, $(\bar E,0,\tilde{\mathbf 0})\in\mathcal S_0$, and $(\bar X,\bar\nu)$ solves the associated fluid equations. Then:
--
--   1. $\bar X(t)=\langle\mathbf 1,\bar\nu_t\rangle$ for every $t\ge0$;
--   2. $\bar X$ is nondecreasing on $[0,\infty)$ and $\bar X(t)\to\bar\lambda$ as $t\to\infty$;
--   3. $\bar\nu_t$ converges weakly, monotonically up to $\bar\lambda\bar\nu_*$: for every nonnegative bounded continuous $f$, $t\mapsto\langle f,\bar\nu_t\rangle$ is nondecreasing on $[0,\infty)$ and
--   $$\lim_{t\to\infty}\langle f,\bar\nu_t\rangle=\bar\lambda\,\langle f,\bar\nu_*\rangle=\bar\lambda\int_{[0,\infty)}f(x)(1-G(x))\,dx .$$
--
--   This is Theorem 3.9(1) as the paper proves it: an empty system fed at a rate no larger than its capacity fills up monotonically to the equilibrium occupancy.
--
--   **Formalization Note** "Increases" is read as nondecreasing. Test functions are bounded continuous functions on $\mathbb R$; since every $\bar\nu_t$ and $\bar\nu_*$ are carried by $[0,M)$, this is equivalent to testing against bounded continuous functions on $[0,M)$. The limit measure is $\bar\lambda\bar\nu_*$ written as the scalar multiple by $\bar\lambda\ge0$ in $[0,\infty]$.
-- source:
--   Kaspi and Ramanan, Law of Large Numbers Limits for Many-Server Queues, Ann. Appl. Probab. 21(1) (2011), p. 105, Proposition 6.1(2); definition of monotone weak convergence, p. 47

import Mathlib
import Definitions.Def_ManyServerFluid_Equilibrium_Model
import Definitions.Def_ManyServerFluid_Equilibrium_Renewal
open MeasureTheory Filter Topology Set BoundedContinuousFunction

namespace ManyServerFluid.Equilibrium

/-- Proposition 6.1(2) (p. 105): with constant arrival rate λ̄ ∈ [0, 1] and an empty start,
X̄(t) = ⟨1, ν̄_t⟩ increases to λ̄ and ν̄_t converges weakly monotonically up to λ̄ν̄*. -/
theorem proposition_6_1_2 (S : ServiceLaw) (hA2 : S.Assumption2)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (X : ℝ → ℝ) (ν : ℝ → FiniteMeasure ℝ)
    (hS0 : S.InS0 (fun t => c * t) 0 0) (hsol : S.IsFluidSolution (fun t => c * t) 0 0 X ν) :
    (∀ t, 0 ≤ t → X t = ((ν t).mass : ℝ)) ∧ MonotoneOn X (Ici 0) ∧ Tendsto X atTop (𝓝 c) ∧
    MonoWeakUpTo (fun t => (ν t : Measure ℝ)) (ENNReal.ofReal c • S.nuStar) := by sorry

end ManyServerFluid.Equilibrium
