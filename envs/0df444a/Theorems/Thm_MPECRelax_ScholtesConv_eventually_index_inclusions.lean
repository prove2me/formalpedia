-- Prove2me | Theorems.Thm_MPECRelax_ScholtesConv_eventually_index_inclusions
-- name    : MPECRelax.ScholtesConv.eventually_index_inclusions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:51:52.993609+00:00
-- url     : https://prove2.me/theorems/925d1dd5-d837-42e3-82be-f6b25abcfdf7
-- title:
--   Proof of Theorem 3.1, p. 9 — eventual inclusions I_g(x^k) ⊆ I_g, I_G(x^k) ⊆ I_00 ∪ I_0+, I_H(x^k) ⊆ I_00 ∪ I_+0
-- statement:
--   Let the MPEC data $f,g,h,G,H$ be continuously differentiable, let $\{t_k\}\downarrow0$ (that is, $t_k>0$, $t_k$ nonincreasing and $t_k\to0$), let $x^k\in X^S(t_k)$ be feasible for Scholtes' relaxed program $R^S(t_k)$ for every $k$, and let $x^k\to x^*$. Then for all sufficiently large $k$
--
--   $$I_g(x^k)\subseteq I_g,\qquad I_G(x^k)\subseteq I_{00}\cup I_{0+},\qquad I_H(x^k)\subseteq I_{00}\cup I_{+0},$$
--
--   where the index sets on the right are those of the limit $x^*$ and those on the left are the active sets at $x^k$.
--
--   These inclusions localise the active constraints of the relaxed programs and are used to control the supports of the multipliers in the proof of Theorem 3.1.
--
--   **Formalization Note** In Theorem 3.1 the iterates are stationary, hence feasible; this milestone only assumes feasibility, which is all the paper's sentence uses. Feasibility of $x^*$ for the MPEC is not assumed. "For all $k$ sufficiently large" is `∀ᶠ k in atTop`.
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, p. 9, proof of Theorem 3.1 (last sentence of the page)

import Mathlib
import Definitions.Def_MPECRelax_ScholtesConv_NLP
import Definitions.Def_MPECRelax_ScholtesConv_MPEC
import Definitions.Def_MPECRelax_ScholtesConv_Scholtes

open Filter Topology

namespace MPECRelax.ScholtesConv

theorem eventually_index_inclusions {n m p l : ℕ} (P : MPEC n m p l) (hP : P.IsC1)
    (t : ℕ → ℝ) (ht_pos : ∀ k, 0 < t k) (ht_anti : Antitone t)
    (ht_lim : Tendsto t atTop (𝓝 0))
    (x : ℕ → E n) (hx : ∀ k, (P.RS (t k)).Feasible (x k))
    (xs : E n) (hxs : Tendsto x atTop (𝓝 xs)) :
    ∀ᶠ k in atTop, P.Ig (x k) ⊆ P.Ig xs ∧ P.IG (x k) ⊆ P.I00 xs ∪ P.I0p xs ∧
      P.IH (x k) ⊆ P.I00 xs ∪ P.Ip0 xs := by sorry

end MPECRelax.ScholtesConv
