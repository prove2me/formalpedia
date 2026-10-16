-- Prove2me | Theorems.Thm_HiringLP_SimUpper_theorem_4
-- name    : HiringLP.SimUpper.theorem_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:48.333362+00:00
-- url     : https://prove2.me/theorems/bd530b16-bc16-41aa-8878-15d615f68df4
-- title:
--   Theorem 4 — for every ε > 0 and τ ∈ (0, 1) some τ-bounded instance gives no value-ordered policy more than (β^τ_k + ε) OPT_sim(I)
-- statement:
--   In Simultaneous Offering (with overage cost $1$ and candidates labelled so that $v_1 \ge \cdots \ge v_n$), a value-ordered policy sends offers to the $m$ highest-valued candidates $\{1, \dots, m\}$ for some $m \in [n]$. For $k \ge 1$ and $\tau \in (0,1)$ let
--   $$
--   \beta^\tau_k = \sup_{s \ge 0}\left(s - \frac{s}{\tau} + \frac{\mathbb{E}[\min\{\mathrm{Pois}(sk), k\}]}{\tau k}\right).
--   $$
--
--   **Theorem.** For every number of positions $k \ge 1$, every $\varepsilon > 0$ and every $\tau \in (0,1)$ there is an instance $I \in \mathcal{I}^\tau_{\mathrm{sim}}$ with $k$ positions (all values at least $\tau$) such that for every $m \in [n]$
--   $$
--   R(I, \{1, \dots, m\}) \le (\beta^\tau_k + \varepsilon)\, \mathrm{OPT}_{\mathrm{sim}}(I),
--   $$
--   where $R(I, S)$ is the expected reward of offering to $S$ and $\mathrm{OPT}_{\mathrm{sim}}(I)$ the best expected reward over all offer sets.
--
--   Together with Theorem 3 (value-ordered policies can guarantee $\alpha^\tau_k$ of the LP bound) this brackets what value-ordered policies can guarantee on $\tau$-bounded instances between $\alpha^\tau_k$ and $\beta^\tau_k$.
--
--   **Formalization Note.** The page leaves $k$ implicit in $\beta^\tau_k$; the theorem is stated for every $k \ge 1$ and the instance is required to have exactly $k$ positions. The instance is existential, of any size $n$; validity includes $1 \le k \le n$, $p \in [0,1]^n$, $v \ge 0$ and sorted labels, so value-ordered policies are the prefixes of the labelling. $\mathrm{OPT}_{\mathrm{sim}}$ is the maximum over all offer sets, not over value-ordered ones.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. 30, Theorem 4

import Mathlib
import Definitions.Def_HiringLP_SimUpper_Model
import Definitions.Def_HiringLP_SimUpper_Constants

namespace HiringLP.SimUpper

/-- Theorem 4 (p. 30): for every number of positions `k ≥ 1`, every `ε > 0` and `τ ∈ (0, 1)`
there is a valid, sorted, `τ`-bounded instance with `k` positions on which every value-ordered
policy earns at most `(β^τ_k + ε) · OPT_sim(I)`. -/
theorem theorem_4 (k : ℕ) (hk : 1 ≤ k) (ε τ : ℝ) (hε : 0 < ε) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ∃ (n : ℕ) (I : SimInstance n), I.Valid ∧ I.k = k ∧ I.TauBounded τ ∧
      ∀ m : ℕ, 1 ≤ m → m ≤ n → reward I (valueOrdered m) ≤ (beta k τ + ε) * OPTsim I := by sorry

end HiringLP.SimUpper
