-- Prove2me | Theorems.Thm_MonoidProdQ_lemma_20
-- name    : MonoidProdQ.lemma_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:59:09.662204+00:00
-- url     : https://prove2.me/theorems/63579d6d-7880-4e93-9542-80942db50d0a
-- title:
--   Lemma 20: $\kappa_G(M)=\beta_G(M)$, and product-preserving subwords keep every essential position
-- statement:
--   Let $M$ be a finite commutative aperiodic monoid and $G\subseteq M$. With $p_x(T)=\prod_{i\in T}x_i$ and $\mathrm{Ess}_x(T)=\{i\in T: p_x(T)\ne p_x(T\setminus\{i\})\}$ for words $x\in G^s$:
--
--   1. the essential width of the subset-product summary equals the product breadth,
--   $$\kappa_G(M)=\sup_{s\ge0}\sup_{x\in G^s}|\mathrm{Ess}_x([s])|=\beta_G(M);$$
--   2. every deletion-essential position of a revealed subword is retained by every product-preserving subword of it: for every $s$, every $x\in G^s$ and all $S\subseteq T\subseteq[s]$,
--   $$p_x(S)=p_x(T)\ \Longrightarrow\ \mathrm{Ess}_x(T)\subseteq S.$$
--
--   Part 2 is the uniform statement that bounds the essential width of every revealed set by $\beta_G(M)$; part 1 records that this bound is exact.
--
--   Differences from the source:
--   - encoding: quantities that may be infinite ($\beta_G(M)$, $\kappa_G(M)$) → values in `ℕ∞`; reason: Lean convention; an unbounded supremum is ⊤ instead of a junk value, same instances
--   - encoding: $G\subseteq M$, words $x\in G^s$ on positions $[s]$ → `G : Finset M`, words `Fin s → ↥G`, $[s]$ = `Finset.univ : Finset (Fin s)`; reason: Lean convention; positions are 0-based, same instances
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Lemma 20 (Preserving subwords and essential width), pp.33–34

import Definitions.Def_MonoidProdQ_IsAperiodic
import Definitions.Def_MonoidProdQ_productBreadth
import Definitions.Def_MonoidProdQ_kappaG

namespace MonoidProdQ

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Lemma 20 (Preserving subwords and essential width), pp.33–34, in the standing setting
of §5 (p.33: "M is a finite commutative aperiodic monoid and G ⊆ M is the allowed alphabet"):
(i) `κ_G(M) = β_G(M)` (Eq. (17) and Eq. (1)); (ii) "every deletion-essential position of a
revealed subword is retained by every product-preserving subword of it": for every word
`x ∈ G^s`, every `T ⊆ [s]` and every `S ⊆ T` with `pₓ(S) = pₓ(T)`, `Essₓ(T) ⊆ S`. -/
theorem lemma_20 {M : Type*} [CommMonoid M] [Finite M] [DecidableEq M] (hM : IsAperiodic M)
    (G : Finset M) :
    kappaG G = productBreadth G ∧
      ∀ (s : ℕ) (x : Fin s → G) (S T : Finset (Fin s)), S ⊆ T →
        subsetProd x S = subsetProd x T → subsetEss x T ⊆ S := by sorry

end MonoidProdQ
