-- Prove2me | Theorems.Thm_LinMatroidSecretary_Online_Supplement_lemma_7
-- name    : LinMatroidSecretary.Online.Supplement.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:04:52.833211+00:00
-- url     : https://prove2.me/theorems/b8a059bd-97fa-4b76-afa3-10b774fae2db
-- title:
--   Lemma 7 — feasibility of the XOS allocation LP
-- statement:
--   Let $F$ be a finite field, let $v:E\to F^d$ represent a matroid on a finite labelled ground set, and let the agents be $N=\{0,\ldots,n-1\}$. Fix an agent set $X\subseteq N$ of size $i$, a sample size $1\le k<i$, eligibility sets $E_a$, and bundles $B_a\subseteq E_a$ for $a\in X$. Suppose these bundles are pairwise disjoint and their union is independent. For each $a\in X$, let $\mu_a$ be a probability distribution on subspaces of $F^d$ satisfying
--   $$\mathbb E_{W\sim\mu_a}\dim(W\cap L)\le\left(1-\frac{k}{i-1}\right)\dim L\qquad(L\le F^d).$$
--   Then the allocation LP is feasible:
--   $$\exists p\text{ satisfying all of (22a), (22b), (22c), (22d), (22e).}$$
--   In particular the subset distributions have exact element marginals $k/(i-1)$ and obey $g_p(L)\le0$ for every $L\le V_X=\langle\bigcup_{a\in X}E_a\rangle$. No rationality or support-in-predecessor-span hypothesis is imposed. This establishes the allocation LP's feasibility in the full range of dimension constraints; taking the bundles from $\mathrm{OPT}(X)$ gives the printed lemma.
--
--   Differences from the source:
--   - generalization: the bundles of OPT(X) and predecessor distributions μ_(X−a) → any feasible allocation of X and any probability distributions satisfying (15), without a support-in-predecessor-span or rationality assumption; reason: the setup of §5.3 fixes arbitrary laws satisfying (15); its argument uses only eligibility and feasibility of the bundles, specifically the direct-sum inequality (25), so the source instance specializes to this claim
--   - encoding: a finite set of agents X, labelled items, and the variables of (22a)–(22e) → X ⊆ Fin n, a labelled vector family in F^d, exact finite sums, and irrelevant unconstrained function coordinates outside the LP variable ranges; reason: reindexing finite agents and vectors changes no instances; (22a)–(22e) constrain exactly the specified coordinates and all L ≤ V_X
-- source:
--   Kristóf Bérczi, Shaddin Dughmi, Vasilis Livanos, Jose Soto, Victor Verdugo, The Strong Secretary Conjecture is True for Linear Matroids, STOC 2027 submission #608 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/608.pdf, Lemma 7, PDF p. 24 (printed p. 22)

import Mathlib
import Definitions.Def_LinMatroidSecretary_Online_Supplement_Allocation
import Definitions.Def_LinMatroidSecretary_Online_Supplement_BundleLP

namespace LinMatroidSecretary.Online.Supplement

/-- Lemma 7, STOC 2027 #608, PDF p. 24 (printed p. 22), generalized as permitted by
the setup of §5.3: any feasible bundles, any predecessor distributions satisfying (15).
Optimality, rational coefficients, and support in predecessor spans are not hypotheses. -/
theorem lemma_7 {F : Type} [Field F] [Fintype F] {d n : ℕ}
    {E : Type} [Fintype E] [DecidableEq E] (v : E → Fin d → F)
    (elig : Fin n → Finset E) (X : Finset (Fin n)) (k : ℕ)
    (hk : 1 ≤ k) (hki : k < X.card) (B : Fin n → Finset E)
    (hB : FeasibleOn (linMatroid (F := F) v) elig X B)
    (μ : Fin n → Dist F d)
    (hμ : ∀ a ∈ X, IsDistOn (μ a) ⊤ ∧ DimInvariant (μ a) (X.card - 1) k) :
    ∃ p : Fin n → SelectionRule F d E, BundleLPFeasible v elig X k B μ p := by sorry

end LinMatroidSecretary.Online.Supplement
