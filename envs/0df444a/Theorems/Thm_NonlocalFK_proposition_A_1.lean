-- Prove2me | Theorems.Thm_NonlocalFK_proposition_A_1
-- name    : NonlocalFK.proposition_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:43:33.583795+00:00
-- url     : https://prove2.me/theorems/d01447e7-5251-4be7-a3fc-d18e34c85a77
-- title:
--   Proposition A.1 — Feynman–Kac representation for local terminal and boundary data
-- statement:
--   Let $g$ be bounded on $\partial_pQ$ and continuous on $\partial_pQ\setminus D$, with $D$ a small set as in Assumption 2.1. Then the problem
--
--   $$
--   -\frac{\partial w}{\partial t}-\mathcal Lw=f\ \text{ in }Q,\qquad w=g\ \text{ on }\partial_pQ
--   $$
--
--   has a unique bounded solution $w\in C^{1,2}(Q)\cap C(\bar Q\setminus D)$, and for all $(t,x)\in\bar Q$,
--
--   $$
--   w(t,x)=E_t^x\Big[\int_t^{\tau\wedge T}e^{-r(s-t)}f(s,\xi_s)\,ds+e^{-r((\tau\wedge T)-t)}g(\tau\wedge T,\xi_{\tau\wedge T})\Big],
--   $$
--
--   where $\xi$ is the diffusion $d\xi_s=b(s,\xi_s)\,ds+\sigma(s,\xi_s)\,dB_s$ started from $x$ at time $t$ and $\tau$ is the first time $\xi$ hits $\partial\mathcal O$.
--
--   This extends the classical Feynman–Kac representation for Dirichlet problems to data with discontinuities in $D$. Each step of the iteration of §3 is an instance of it.
--
--   Differences from the source:
--   - encoding: bounded smooth domain → open, connected, bounded, with a global $C^\infty$ defining function $\rho$; reason: equivalent for bounded domains; the paper gives no degree of smoothness, read as $C^\infty$
--   - encoding: $f$ uniformly Hölder on $\bar Q$ with exponent $\alpha$ → Hölder for the metric of $\mathbb R\times\mathbb R^d$ with an existential $\alpha\in(0,1]$; reason: with $\alpha$ existential this and the parabolic Hölder class coincide on the bounded set $\bar Q$
--   - reading: $d$-dimensional balls, open or closed not specified → open balls; reason: the two readings agree, since $\varepsilon$ is arbitrary and balls can be slightly enlarged
--   - generalization: $h$ with $D$ the set of its discontinuity points → any $g$ continuous off a small closed set $D$; reason: Lemma A.2 and Step 1 of Theorem 3.1 apply the result in this form, with data that may be continuous at points of $D$; the printed case is contained
--   - encoding: $E_t^x$ for the diffusion $\xi$ → $w(t,x)$ is the expectation under every `LocalRealization`, one of which exists; reason: the filtered space is part of the data, and the existence clause keeps the representation from being vacuous
--   - encoding: "the unique bounded solution" → every bounded solution agrees with $w$ on $\bar Q$; reason: values off $\bar Q$ are not part of a solution
--   - encoding: the expectation in the statement → integrability of the functional is asserted explicitly; reason: the paper's expectation presupposes it; without it a Bochner integral defaults to $0$
--   - generalization: §2's standing assumptions → only those on the local data; reason: $\nu$ and Assumption 2.2 do not occur in the proposition
-- source:
--   Dai, Kou, Yang, A Stochastic Representation for Nonlocal Parabolic PDEs with Applications, SSRN 3541591, Proposition A.1, eq. (A.3)-(A.4), p.23

import Definitions.Def_NonlocalFK_IsSmallSet
import Definitions.Def_NonlocalFK_IsBoundedSolution
import Definitions.Def_NonlocalFK_LocalRealization

open MeasureTheory Set

universe u

namespace NonlocalFK

/-- Proposition A.1 (Feynman-Kac Representation for Local Terminal and Boundary Data) (Dai, Kou,
Yang, SSRN 3541591, p.23): if `g` is bounded on `∂ₚQ` and continuous on `∂ₚQ ∖ D`, with `D` as in
Assumption 2.1, the problem `−∂w/∂t − 𝓛w = f` in `Q`, `w = g` on `∂ₚQ` has a unique bounded solution
`w ∈ C^{1,2}(Q) ∩ C(Q̄ ∖ D)`, and it is represented by (A.3) for all `(t, x) ∈ Q̄`, where `ξ` is the
diffusion (A.4) started from `x` at time `t`.

**Formalization Note.** The paper calls the data `h` and takes `D` to be its set of discontinuity
points. Here `D` is any set as in Assumption 2.1 off which `g` is continuous, which is the form
Lemma A.2 and the proof of Theorem 3.1 use. Uniqueness is agreement on `Q̄`, since values off `Q̄`
are not part of a solution. The clause that a realization of `ξ` exists keeps (A.3) from being
vacuous. -/
theorem proposition_A_1 {d : ℕ} (c : Diffusion d) (hc : c.Assumptions) (D : Set (ℝ × E d))
    (hD : IsSmallSet c D) (g : ℝ × E d → ℝ) (hg : ∃ C : ℝ, ∀ p ∈ c.bdry, |g p| ≤ C)
    (hgc : ContinuousOn g (c.bdry \ D)) :
    ∃ w : ℝ × E d → ℝ, c.IsBoundedSolution D g w ∧
      (∀ w' : ℝ × E d → ℝ, c.IsBoundedSolution D g w' → EqOn w' w c.Qbar) ∧
      (∀ p ∈ c.Qbar, ∃ (Ω : Type u) (_ : MeasurableSpace Ω),
        Nonempty (LocalRealization c p.1 p.2 Ω)) ∧
      ∀ p ∈ c.Qbar, ∀ (Ω : Type u) [MeasurableSpace Ω] (R : LocalRealization c p.1 p.2 Ω),
        Integrable (R.payoff g) R.P ∧ w p = ∫ ω, R.payoff g ω ∂(R.P) := by sorry

end NonlocalFK
