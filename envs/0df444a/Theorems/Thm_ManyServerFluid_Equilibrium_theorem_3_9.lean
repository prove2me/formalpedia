-- Prove2me | Theorems.Thm_ManyServerFluid_Equilibrium_theorem_3_9
-- name    : ManyServerFluid.Equilibrium.theorem_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:33.102309+00:00
-- url     : https://prove2.me/theorems/c0314544-1964-4eef-84cb-4640081777d9
-- title:
--   Theorem 3.9 — the fluid age measure converges to the equilibrium measure ν̄*(dx) = (1 − G(x))dx
-- statement:
--   Suppose Assumption 2 holds: for some $m_0<M$ the hazard rate $h$ is bounded or lower semicontinuous on $(m_0,M)$. Let $\bar\nu_*(dx)=(1-G(x))\,dx$ on $[0,M)$.
--
--   1. Let $\bar\lambda\in[0,1]$, let $(\bar\lambda\,\mathrm{id},\bar X(0),\bar\nu_0)\in\mathcal S_0$ with $\bar X(0)=0$, and let $(\bar X,\bar\nu)$ solve the associated fluid equations. Then $\bar X(t)=\langle\mathbf 1,\bar\nu_t\rangle$ for every $t\ge0$, $\bar X$ is nondecreasing with $\bar X(t)\to\bar\lambda$, and $\bar\nu_t$ converges weakly, monotonically up to $\bar\lambda\bar\nu_*$: for every nonnegative bounded continuous $f$, $t\mapsto\langle f,\bar\nu_t\rangle$ is nondecreasing and tends to $\bar\lambda\langle f,\bar\nu_*\rangle$.
--   2. If the service distribution has a finite second moment, $\int x^2g(x)\,dx<\infty$, then for every initial condition $(\mathrm{id},\bar X(0),\bar\nu_0)\in\mathcal S_0$ and every solution $(\bar X,\bar\nu)$ of the associated fluid equations, $\bar\nu_t$ converges weakly to $\bar\nu_*$: for every bounded continuous $f$,
--   $$\lim_{t\to\infty}\langle f,\bar\nu_t\rangle=\langle f,\bar\nu_*\rangle=\int_{[0,\infty)}f(x)\big(1-G(x)\big)\,dx.\qquad(3.14)$$
--
--   Part 2 says that a critically loaded many-server fluid queue ($\bar E=\mathrm{id}$, arrival rate equal to service capacity) forgets its initial condition: whatever the initial number of customers and their ages, the age distribution of customers in service converges to the stationary excess distribution of $G$, the invariant state of Remark 3.8.
--
--   **Formalization Note** The paper's "let $(\bar X,\bar\nu)$ be the unique solution" is a hypothesis that $(\bar X,\bar\nu)$ is a solution; uniqueness (Theorem 3.5) is the subject of the companion mission and is not needed to state the result. Weak convergence in part 2 is against all bounded continuous functions (not only compactly supported ones), and is tested with bounded continuous functions on $\mathbb R$, which is equivalent to $\mathcal C_b[0,\infty)$ (extend by $f(\max(x,0))$). "Increases" is read as nondecreasing; the monotone conclusion of part 1 is kept in full. The second moment is the integrability of $x\mapsto x^2g(x)$. The paper's proof of part 2 compares the given solution with the solution started empty, whose existence it takes from its Theorem 3.7; that solution is explicit (Proposition 6.1(1)–(2), Remark 3.8 and Lemma 3.4), but a proof of this statement must construct it.
-- source:
--   Kaspi and Ramanan, Law of Large Numbers Limits for Many-Server Queues, Ann. Appl. Probab. 21(1) (2011), p. 47, Theorem 3.9, (3.14), and the definition of monotone weak convergence before it; proof pp. 107, 111–112

import Mathlib
import Definitions.Def_ManyServerFluid_Equilibrium_Model
import Definitions.Def_ManyServerFluid_Equilibrium_Renewal
open MeasureTheory Filter Topology Set BoundedContinuousFunction

namespace ManyServerFluid.Equilibrium

/-- Theorem 3.9 (p. 47): under Assumption 2, (1) from an empty start with arrival rate λ̄ ∈ [0, 1],
X̄(t) = ⟨1, ν̄_t⟩ increases to λ̄ and ν̄_t converges weakly monotonically up to λ̄ν̄*; (2) if G has a
finite second moment and Ē = id, ν̄_t converges weakly to ν̄* from every initial condition. -/
theorem theorem_3_9 (S : ServiceLaw) (hA2 : S.Assumption2) :
    (∀ (lam X0 : ℝ) (ν0 : FiniteMeasure ℝ) (X : ℝ → ℝ) (ν : ℝ → FiniteMeasure ℝ),
      0 ≤ lam → lam ≤ 1 → S.InS0 (fun t => lam * t) X0 ν0 →
      S.IsFluidSolution (fun t => lam * t) X0 ν0 X ν → X0 = 0 →
      (∀ t, 0 ≤ t → X t = ((ν t).mass : ℝ)) ∧ MonotoneOn X (Ici 0) ∧ Tendsto X atTop (𝓝 lam) ∧
      MonoWeakUpTo (fun t => (ν t : Measure ℝ)) (ENNReal.ofReal lam • S.nuStar)) ∧
    (Integrable (fun x => x ^ 2 * S.g x) →
      ∀ (X0 : ℝ) (ν0 : FiniteMeasure ℝ) (X : ℝ → ℝ) (ν : ℝ → FiniteMeasure ℝ),
      S.InS0 (fun t => t) X0 ν0 → S.IsFluidSolution (fun t => t) X0 ν0 X ν →
      ∀ f : ℝ →ᵇ ℝ,
        Tendsto (fun t => ∫ x, f x ∂(ν t : Measure ℝ)) atTop (𝓝 (∫ x, f x ∂S.nuStar))) := by sorry

end ManyServerFluid.Equilibrium
