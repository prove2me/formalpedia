-- Prove2me | Theorems.Thm_HDXNbhdPCP_Main_corollary_6_6
-- name    : HDXNbhdPCP.Main.corollary_6_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:59:41.838218+00:00
-- url     : https://prove2.me/theorems/572d45a6-897e-4725-8546-296e82c1ab04
-- title:
--   Corollary 6.6 — density of the opposite complex, $\theta_{I,\emptyset}\ge1-2|I|/q$
-- statement:
--   Let $K=\mathbb F_q$ be a finite field, $V=K^n$, $\mathcal X=\mathcal X(V)$ its spherical building (uniform distribution on maximal flags), $\sigma=(E_1<\dots<E_{n-1})$ a maximal flag and $O=O_\sigma(V)$ the opposite complex. For every nonempty set of colours $I\subseteq\{1,\dots,n-1\}$,
--   $$\theta_{I,\emptyset}=\Pr_{R\sim\mathcal X[I]}\big[R\in O[I]\big]\ \ge\ 1-\frac{2|I|}{q}.$$
--
--   It lets soundness of agreement tests on buildings be transferred to opposite complexes, hence to links of KMS complexes (Lemma 6.11).
--
--   Differences from the source:
--   - encoding: an n-dimensional space V over F_q; X(V); colours i = dimensions → V = Fin n → K for a finite field K with q = |K|; colours BColor n = {1, …, n − 1}; vertices Submodule K V; reason: every n-dimensional F_q-space is isomorphic to K^n
--   - reading: O_σ(V) defined (Definition 6.3) from the standard flag of an ordered basis, while the corollary fixes any maximal flag σ → O_σ for an arbitrary maximal flag E (IsMaxFlag); reason: every maximal flag is the standard flag of some ordered basis
-- source:
--   Dikstein, Dinur, Hopkins, Singer, Sounder, shorter, and simpler PCPs from HDX neighborhoods, STOC 2027 submission (manuscript sha256 7dcb1b53…), p. 40, Corollary 6.6 (θ defined p. 39)

import Mathlib
import Definitions.Def_HDXNbhdPCP_Main_Complex
import Definitions.Def_HDXNbhdPCP_Main_Building

namespace HDXNbhdPCP.Main

/-- Corollary 6.6: density of the opposite complex, `θ_{I,∅} ≥ 1 − 2|I|/q`. -/
theorem corollary_6_6 (K : Type) [Field K] [Fintype K] (n : ℕ)
    (E : BColor n → Submodule K (Fin n → K)) (hE : IsMaxFlag K E)
    (I : Finset (BColor n)) (hI : I.Nonempty) :
    thetaEmpty K n E I ≥ 1 - 2 * (I.card : ℝ) / (Fintype.card K : ℝ) := by sorry

end HDXNbhdPCP.Main
