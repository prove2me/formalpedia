-- Prove2me | Theorems.Thm_MerkleROM_VerifierLowerBound_disjoint_product
-- name    : MerkleROM.VerifierLowerBound.disjoint_product
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T22:34:04.625567+00:00
-- url     : https://prove2.me/theorems/2f9e3506-f3f0-4e33-aaed-9d82b072e5ef
-- title:
--   Lemma 6.1 — Disjoint Product Lemma
-- statement:
--   Let $X$ be any set, let $R:X\to\{0,1\}^{\lambda}$ be a uniform random oracle, and let $V$ be a deterministic local verifier that receives and queries a set of at most $k$ points. Let $Q,t\in\mathbb N$ and let $\eta\in\mathbb R$. Suppose every possibly randomized $(Q+tk)$-query algorithm finds an accepted set with probability at most $\eta$. Then every possibly randomized $Q$-query algorithm has
--
--   $$\Pr[W_1,\ldots,W_t\text{ are disjoint and all accepted}]\le e^{tk}\eta^t.$$
--
--   The search may be adaptive and need not query its output points. The input domain is not required to be finite or nonempty. Zero success probability is allowed. For $t=0$, the output is the empty family and the upper bound is one, using $\eta^0=1$.
--
--   This is the exact disjoint product lemma, also stated as Lemma 1.1, with its full query budget and exponential loss.
--
--   Differences from the source:
--   - encoding: a random oracle over any set X → consistent lazy finite-query cylinder probabilities, with PMFs over independent randomized probe trees; reason: no Fintype X assumption or independent-oracle replacement is introduced
--   - encoding: t disjoint output sets, without queried-output normalization → actual success evaluated by reading outputs after the bounded search; reason: evaluation determines the event only; it is not charged to the search budget and the Q+tk premise remains unchanged
-- source:
--   Miranda Christ, Oliver Korten, Tal Malkin, Noam Mazor, Shyamal Patel, STOC 2027 submission #1169 (October 2026), Merkle Trees Minimize Verifier Complexity in the ROM, p. 24, Lemma 6.1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1169.pdf

import Definitions.Def_MerkleROM_VerifierLowerBound_protocol
import Definitions.Def_MerkleROM_VerifierLowerBound_product

set_option autoImplicit false
noncomputable section

namespace MerkleROM.VerifierLowerBound

theorem disjoint_product {X : Type} (lam k Q t : ℕ) (V : SetVerifier X lam) (eta : ℝ)
    (hsingle : ∀ A : PMF (Tree X (Bits lam) (Finset X)),
      RandomBounded (Q+t*k) A → singleProbability V k A ≤ eta) :
    ∀ A : PMF (Tree X (Bits lam) (Fin t → Finset X)),
      RandomBounded Q A → multiProbability V k A ≤ Real.exp ((t*k : ℕ) : ℝ) * eta^t := by sorry

end MerkleROM.VerifierLowerBound
