-- Prove2me | Theorems.Thm_HeteroBass_HetP_Supplement_lemma_2
-- name    : HeteroBass.HetP.Supplement.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:29:35.50101+00:00
-- url     : https://prove2.me/theorems/38fec184-baa0-4125-b307-c0339e87bb93
-- title:
--   Lemma 2 — all subset master equations and initial conditions
-- statement:
--   Consider the finite heterogeneous Bass model on $M>0$ consumers, initially empty, with $p_i\ge0$ and nonnegative directed off-diagonal rates $Q_{k,i}$. Each node has positive total incoming influence, as in (7). Let $s_U(t)$ be the probability that every node in $U$ is still a nonadopter, as observed from the published transition matrix. For every proper nonempty subset $U$ and every $t\ge0$,
--
--   $$s_U'(t)=-\left(\sum_{i\in U}p_i+\sum_{l\notin U}\sum_{i\in U}Q_{l,i}\right)s_U(t)
--    +\sum_{l\notin U}\left(\sum_{i\in U}Q_{l,i}\right)s_{U\cup\{l\}}(t).$$
--
--   For the full node set $V$, and with all initial conditions, the remaining clauses are
--
--   $$s_V'(t)=-\left(\sum_i p_i\right)s_V(t),\qquad s_U(0)=1\quad(\varnothing\ne U\subseteq V).$$
--
--   This result supplies the general master equations used in Appendix K to obtain the two-sided circle equations. It retains arbitrary network structure, every proper nonempty subset, the full-set equation, and the initial data.
--
--   Differences from the source:
--   - encoding: distinct indexed node subsets and their complement in (19) → Finsets of Fin M, complementary finite sums and insert l U; reason: sets enforce distinctness and remove dependence on the enumeration; Q_{l,i} always points from outside the nonadopter set into it
--   - encoding: time derivatives of probabilities from an initially empty finite process with rate assumptions (4)–(7) → HasDerivWithinAt on [0,∞), explicit nonnegative rates and positive incoming totals, and M>0; reason: physical time starts at zero; the right derivative there and the standing finite rate domain are explicit, and diagonal Q values are irrelevant
-- source:
--   Fibich & Golan, Diffusion of new products with heterogeneous consumers, arXiv:2102.05926v3, Lemma 2, (19a)–(19c), p. 7; Appendix A, p. 24

import Mathlib
import Definitions.Def_HeteroBass_HetP_Supplement_Subset

namespace HeteroBass.HetP.Supplement

theorem lemma_2 {M : ℕ} (hM : 0 < M) (p : Fin M → ℝ)
    (Q : Fin M → Fin M → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hQ : ∀ k j, k ≠ j → 0 ≤ Q k j)
    (hin : ∀ j, 0 < ∑ k ∈ Finset.univ.erase j, Q k j) :
    (∀ U : Finset (Fin M), U.Nonempty → U ≠ Finset.univ →
      ∀ t : ℝ, 0 ≤ t →
        HasDerivWithinAt (subsetNonadoption p Q U)
          (-((∑ i ∈ U, p i) + ∑ l ∈ Uᶜ, ∑ i ∈ U, Q l i) * subsetNonadoption p Q U t
            + ∑ l ∈ Uᶜ, (∑ i ∈ U, Q l i) * subsetNonadoption p Q (insert l U) t)
          (Set.Ici 0) t) ∧
    (∀ t : ℝ, 0 ≤ t →
      HasDerivWithinAt (subsetNonadoption p Q Finset.univ)
        (-(∑ i, p i) * subsetNonadoption p Q Finset.univ t) (Set.Ici 0) t) ∧
    (∀ U : Finset (Fin M), U.Nonempty → subsetNonadoption p Q U 0 = 1) := by sorry

end HeteroBass.HetP.Supplement
