-- Prove2me | Theorems.Thm_LipStableCA_lemma_5_3
-- name    : LipStableCA.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:54:36.275537+00:00
-- url     : https://prove2.me/theorems/3e91de62-a534-4888-8ecf-ff1e743c491e
-- title:
--   Lemma 5.3 — the taxation principle
-- statement:
--   Let $(S,p)$ be a deterministic truthful mechanism. Fix a bidder $i$ and reports $v_{-i}$ of the other bidders, and call a bundle $Q$ attained if $S_i(v_i',v_{-i})=Q$ for some $v_i'\in\mathcal V$. Then every attained bundle $Q$ has a price $\pi(Q)\in\mathbb R$ such that
--
--   1. $p_i(v_i',v_{-i})=\pi(Q)$ whenever $S_i(v_i',v_{-i})=Q$, and
--   2. for every $v_i\in\mathcal V$, the bundle $S_i(v_i,v_{-i})$ maximizes $v_i(Q)-\pi(Q)$ over all attained bundles $Q$.
--
--   So a truthful mechanism presents each bidder with a menu of bundles and prices.
--
--   Differences from the source:
--   - encoding: a price on the attained bundles → a function $\pi$ on all bundles, used on attained ones; reason: its values elsewhere play no role
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Lemma 5.3, p.21

import Definitions.Def_LipStableCA_Mechanism
import Definitions.Def_LipStableCA_offerBundle

namespace LipStableCA

/-- **Lemma 5.3.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.21. **Formalization Note.** a function `π` on all bundles, used on attained ones: its values elsewhere play no role. -/
theorem lemma_5_3 {n m : ℕ} (S : Profile n m → Alloc n m) (p : Profile n m → Fin n → ℝ)
    (h : IsTruthful S p) (i : Fin n) (v : Profile n m) (hv : IsProfile v) :
    ∃ π : Finset (Fin m) → ℝ,
      (∀ u, IsValuation u → p (Function.update v i u) i = π ((S (Function.update v i u)).1 i)) ∧
      (∀ u, IsValuation u → ∀ Q, IsAttained S i v Q →
        u Q - π Q ≤ u ((S (Function.update v i u)).1 i) - π ((S (Function.update v i u)).1 i)) := by sorry

end LipStableCA
