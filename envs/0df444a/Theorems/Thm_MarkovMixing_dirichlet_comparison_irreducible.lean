-- Prove2me | Theorems.Thm_MarkovMixing_dirichlet_comparison_irreducible
-- name    : MarkovMixing.dirichlet_comparison_irreducible
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:10:38.371086+00:00
-- url     : https://prove2.me/theorems/b6ec4685-0d93-42d4-b548-b7b405a6e5eb
-- title:
--   Lemma 13.22 -- comparison of Dirichlet forms
-- statement:
--   Let $P$ and $\tilde P$ be two Markov chains on the same finite state space $V$ of at least two states, each **irreducible** (from any state, any other is reachable in some number of steps) and each **reversible** with respect to its own stationary distribution — $\pi$ for $P$, $\tilde\pi$ for $\tilde P$ — meaning the detailed balance equations $\pi(x)P(x,y)=\pi(y)P(y,x)$ hold, and likewise for $\tilde P,\tilde\pi$. Assume $\tilde\pi$ is strictly positive.
--
--   Two notions carry the argument. The **Dirichlet form** of $P$ at a function $f:V\to\mathbb R$ is
--   $$\mathcal E(f)=\tfrac12\sum_{x,y}\pi(x)P(x,y)\bigl(f(x)-f(y)\bigr)^2,$$
--   the average squared change of $f$ across one step of the chain in equilibrium — a measure of how much the chain moves $f$ around. The **spectral gap** is $\gamma=1-\lambda_2$, where $\lambda_2$ is the largest eigenvalue of $P$ other than $1$; $\tilde\gamma$ is defined the same way from $\tilde P$. The two are linked by the variational characterization: $\gamma$ is the minimum of $\mathcal E(f)/\operatorname{Var}_\pi(f)$ over non-constant $f$.
--
--   **The comparison lemma** (Levin–Peres–Wilmer, Lemma 13.22) asserts: if some constant $B>0$ dominates one Dirichlet form by the other,
--   $$\tilde{\mathcal E}(f)\le B\,\mathcal E(f)\qquad\text{for every } f:V\to\mathbb R,$$
--   then the spectral gaps obey
--   $$\tilde\gamma\;\le\;\Bigl[\max_{x\in V}\frac{\pi(x)}{\tilde\pi(x)}\Bigr]\,B\,\gamma .$$
--
--   This is the workhorse of the comparison method: to bound the gap of a chain you cannot analyze directly, exhibit a chain you can, bound one Dirichlet form by the other — typically by routing each edge of the hard chain along a path in the easy one — and pay only the two explicit prices, the constant $B$ and the worst-case ratio of stationary weights.
--
--   *A note on the irreducibility hypothesis.* The book states the lemma for reversible chains, but proves it through the variational characterization of Remark 13.13, which is a statement about irreducible chains — and $\lambda_2$, the second eigenvalue counted with multiplicity, agrees with "the largest eigenvalue different from $1$" exactly when $1$ is a simple eigenvalue, which for a reversible chain is irreducibility. Without it the supremum defining $\lambda_2$ can be over an empty set, reported as $0$ by Lean's total $\sup$, so that a chain which does not move at all is credited with the largest possible gap: for $P=\tilde P=I$ on two states both Dirichlet forms vanish identically, the comparison hypothesis holds for *every* $B>0$, and the conclusion would read $1\le B$ for arbitrarily small $B$.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 13.4, Lemma 13.22, Eq. (13.18), p. 181

import Definitions.Def_mm_spectral

namespace MarkovMixing

/-- **Lemma 13.22** (LPW), the comparison of Dirichlet forms: if
`Ẽ(f) ≤ B E(f)` for all `f`, then the spectral gaps satisfy
`γ̃ ≤ [max_x π(x)/π̃(x)] B γ`.

Both chains are hypothesized irreducible. LPW state the lemma for reversible
chains, but its proof runs through the variational characterization of the
spectral gap (Remark 13.13, from Lemma 13.12), which is a statement about
irreducible chains: `lambdaTwo` is the largest eigenvalue *different from* `1`,
which is the book's `λ₂` — the second eigenvalue counted with multiplicity —
exactly when `1` is a simple eigenvalue. Without irreducibility that set can be
empty, `sSup ∅ = 0` gives `γ = 1`, and the conclusion becomes false: for
`P = P' = I` on two states both Dirichlet forms vanish, so the comparison
hypothesis holds for every `B > 0`, while the two gaps are both `1`. -/
theorem dirichlet_comparison_irreducible {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (hV : 2 ≤ Fintype.card V) (P P' : Matrix V V ℝ) (hP : IsStochastic P) (hP' : IsStochastic P')
    (hirr : Irreducible P) (hirr' : Irreducible P')
    (π π' : V → ℝ) (hπ : IsStationary P π) (hπ' : IsStationary P' π')
    (hrev : DetailedBalance P π) (hrev' : DetailedBalance P' π')
    (hpos' : ∀ x : V, 0 < π' x)
    (B : ℝ) (hB : 0 < B)
    (hcomp : ∀ f : V → ℝ, dirichletForm P' π' f ≤ B * dirichletForm P π f) :
    spectralGap P' ≤ (⨆ x : V, π x / π' x) * B * spectralGap P := by
  sorry

end MarkovMixing
