-- Prove2me | Theorems.Thm_JakulinBratko_totalCorrelation_decomposition
-- name    : JakulinBratko.totalCorrelation_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:04:10.497326+00:00
-- url     : https://prove2.me/theorems/5b899947-2302-4099-ad31-485384abbea1
-- title:
--   Eqs. (10)–(11) with Eq. (6): total correlation decomposes into interaction information and vanishes exactly under independence (corrected: k ≥ 2 in Eq. (10))
-- statement:
--   Let $\mathcal A$ be a finite set of attributes with finite alphabets, $P$ a joint law, and $\mathcal S\subseteq\mathcal A$. Then:
--
--   1. (decomposition, Eq. (11)) total correlation is the sum of the interaction informations of the subsets with at least two elements,
--   $$
--   C(\mathcal S)=\sum_{\mathcal T\subseteq\mathcal S,\ |\mathcal T|\ge 2}I(\mathcal T);
--   $$
--   2. (recursion, Eq. (10)) if $|\mathcal S|\ge 2$ and $X\in\mathcal S$, then
--   $$
--   I(\mathcal S)=I(\mathcal S\setminus X\mid X)-I(\mathcal S\setminus X);
--   $$
--   3. (sign, Eq. (6)) $C(\mathcal S)\ge 0$, and $C(\mathcal S)=0$ if and only if the attributes of $\mathcal S$ are mutually independent: for every assignment $\mathbf s$ of $\mathcal S$,
--   $$
--   P(\mathbf s)=\prod_{X\in\mathcal S}P(s_X).
--   $$
--
--   Here $I(\mathcal S\setminus X\mid X)$ is the average over the values $x$ of $X$ of the interaction information under the conditional law given $X=x$. The paper has no labelled theorem, and these displays are its mathematical core: they say that the $k$-way dependence measured by total correlation is a sum of $l$-way interactions, $l\le k$, and that it measures dependence exactly.
--
--   Differences from the source are listed below. The first form of Eq. (10) and the first form of Eq. (11) are the definitions of $I$ and $C$.
--
--   Differences from the source:
--   - correction: Eq. (10) for every X ∈ S and arbitrary k → the recursion under 2 ≤ |S|; reason: false at k = 1: for a fair bit X, I({X}) = -1 while I(∅|X) - I(∅) = 0; the paper's k-way interactions start at 2
--   - reading: I(S \ X|X), defined by the paper only through I(A; B|C) → the average condI P X (S.erase X) of I under the conditional laws; reason: the paper calls this quantity "expected" (p.7) and "average" (p.14); it equals Eq. (4) at |R| = 2
--   - generalization: the sign clause for pairs (p.4) and three attributes (pp.5–6) → the sign clause for every subset S; reason: Eq. (11) is called a decomposition of a k-way dependence, and |S| = 2, 3 give the printed cases
--   - encoding: a probability distribution on attributes {X_1, ..., X_n} → real weights with IsLaw on a Fintype index; P(x) is attrMarg, the marginal of Eq. (8) on the one-point subset read on the alphabet of X; a value of X with P(x) = 0 has weight 0 in condI; reason: Lean convention; same instances
-- source:
--   Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3, §2.4, Eqs. (10)–(11), p.8; §2.3, Eq. (6), pp.5–6

import Definitions.Def_JakulinBratko_IsLaw
import Definitions.Def_JakulinBratko_I
import Definitions.Def_JakulinBratko_C
import Definitions.Def_JakulinBratko_attrMarg
import Definitions.Def_JakulinBratko_condI

namespace JakulinBratko

/-- The goal: §2.4, Eqs. (10)–(11), p.8, with the sign clause of Eq. (6), pp.5–6 (Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3).
For every finite family of finite attributes, every joint law and every subset `S`:
(a) total correlation is the sum of the interaction informations of the subsets with at least two
elements, Eq. (11);
(b) McGill's recursion, Eq. (10), for `2 ≤ |S|` (at `|S| = 1` the printed display is false);
(c) total correlation is nonnegative, and zero exactly when the attributes of `S` are mutually
independent, `P(𝐬) = ∏_{X ∈ S} P(s_X)` at every assignment `𝐬`. -/
theorem totalCorrelation_decomposition {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (P : (∀ i, α i) → ℝ) (hP : IsLaw P)
    (S : Finset ι) :
    C P S = ∑ T ∈ S.powerset with 2 ≤ T.card, I P T ∧
    (2 ≤ S.card → ∀ X ∈ S, I P S = condI P X (S.erase X) - I P (S.erase X)) ∧
    0 ≤ C P S ∧
    (C P S = 0 ↔ ∀ s : (∀ i : S, α i), marg P S s = ∏ X : S, attrMarg P X (s X)) := by sorry

end JakulinBratko
