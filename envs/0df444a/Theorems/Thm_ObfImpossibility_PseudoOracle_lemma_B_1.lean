-- Prove2me | Theorems.Thm_ObfImpossibility_PseudoOracle_lemma_B_1
-- name    : ObfImpossibility.PseudoOracle.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:44.300988+00:00
-- url     : https://prove2.me/theorems/547405cc-afd8-4f9a-af51-41d5cff181da
-- title:
--   Lemma B.1 (= Claim 4.14.2) — a random injection $[K]\to[L]$, $L\ge K^2$, fools every $K^\delta$-query distinguisher up to $1/K^\delta$ w.p. $1-2^{-K^\delta}$
-- statement:
--   There is a constant $\delta>0$ such that the following holds for all sufficiently large $K$ and any $L\ge K^2$. Let $D$ be a distinguisher that makes at most $K^\delta$ oracle queries, and let $G:[K]\to[L]$ be a uniformly random injective function. Then with probability at least $1-2^{-K^\delta}$ over $G$,
--   $$\Big|\Pr_{x\in[K]}\big[D^G(G(x))=1\big]-\Pr_{y\in[L]}\big[D^G(y)=1\big]\Big|\le\frac{1}{K^\delta}.\tag{7}$$
--
--   In words: a random injection is a pseudorandom generator relative to itself. Even a distinguisher that may query $G$ cannot tell an output $G(x)$ for random $x$ from a uniform element of $[L]$, unless it makes many queries, except for a $2^{-K^\delta}$ fraction of the functions $G$. In the paper this is the key step of Proposition 4.14, which builds an oracle relative to which efficient circuit obfuscators exist and so shows that the main impossibility results do not relativize.
--
--   **Formalization Note** $D$ is a family of query trees indexed by its input $y\in[L]$, of depth at most $K^\delta$; it is deterministic and has unbounded computational power between queries. The probability over $G$ is the fraction of embeddings `Fin K ↪ Fin L` at which (7) holds. "Sufficiently large $K$" is an explicit threshold $K_0$; $\delta$ and $K_0$ are chosen before $K$, $L$ and $D$.
-- source:
--   Barak et al., On the (Im)possibility of Obfuscating Programs, J. ACM 59(2) (2012), author's copy, p. A:43, Lemma B.1 (restating Claim 4.14.2, p. A:30)

import Mathlib
import Definitions.Def_ObfImpossibility_PseudoOracle_Setting

namespace ObfImpossibility.PseudoOracle

/-- Lemma B.1 (= Claim 4.14.2), p. A:43: there is a constant `δ > 0` such that for all
sufficiently large `K` and any `L ≥ K²`, every algorithm `D` making at most `K^δ` oracle
queries satisfies, with probability at least `1 - 2^{-K^δ}` over a uniformly random
injective `G : [K] → [L]`,
`|Pr_{x∈[K]}[D^G(G(x)) = 1] - Pr_{y∈[L]}[D^G(y) = 1]| ≤ 1/K^δ`. -/
theorem lemma_B_1 :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K₀ : ℕ, ∀ K L : ℕ, K₀ ≤ K → K ^ 2 ≤ L →
      ∀ D : Fin L → QTree K L, (∀ y, ((D y).depth : ℝ) ≤ (K : ℝ) ^ δ) →
        1 - (2 : ℝ) ^ (-(K : ℝ) ^ δ) ≤
          ((Finset.univ.filter fun G : Fin K ↪ Fin L =>
              |prX D G - prY D G| ≤ 1 / (K : ℝ) ^ δ).card : ℝ) /
            (Fintype.card (Fin K ↪ Fin L) : ℝ) := by sorry

end ObfImpossibility.PseudoOracle
