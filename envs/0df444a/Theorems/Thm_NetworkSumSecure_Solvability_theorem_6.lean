-- Prove2me | Theorems.Thm_NetworkSumSecure_Solvability_theorem_6
-- name    : NetworkSumSecure.Solvability.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T05:05:28.312499+00:00
-- url     : https://prove2.me/theorems/47ed35f6-4e97-416d-af9f-aca3f2e7439a
-- title:
--   Theorem 6 — rank-valid local codes admit feasible user-block transformations
-- statement:
--   Let $N$ be a finite network with $s=|U|$ users, let $r\ge0$, and let $F$ be any finite field with
--
--   $$|F|\ge s+|\mathcal W_r|+1.$$
--
--   Fix arbitrary key counts $z_i\ge0$ and causal local encoding data with global columns $h_e$. Suppose
--
--   $$\operatorname{rank}(H_\rho)\ge r+1,\qquad \operatorname{rank}(H_\rho^{(i)})\ge1\quad\text{for every user }i.$$
--
--   There exist invertible maps $B_i$ on the $1+z_i$ coordinates of each user, new causal local encoding data and a linear server decoder such that
--
--   $$g_e=\widehat B h_e\quad(e\in E),\qquad\widehat B=\operatorname{diag}(B_i),$$
--
--   and the resulting scheme is correct and sum-secure at level $r$. Its private-key assignment is exactly the original $z$. This theorem turns the rank-valid output of Algorithm 1 into an operational feasible scheme.
--
--   **Formalization Note** The sufficient field bound is uniform in the key counts and the initial encoding coefficients. It is a witness for the source's large-field convention, not an optimal field-size assertion.
--
--   Differences from the source:
--   - encoding: a sufficiently large finite field, quantified implicitly → the proof-supported sufficient condition |F|≥s+|W_r|+1, independent of z and the initial code; reason: with η≥r+1 this ensures q^(η-(r+1))(q-s)>|W_r| in (34); no network or rank-valid code is excluded from the eventual field regime
--   - encoding: invertible user matrices and their block-diagonal matrix → invertible linear maps of the standard user-coordinate spaces and their blockwise action on every global column; reason: standard-basis matrices identify these objects exactly; the conclusion also supplies actual local coefficients and a decoder
--   - generalization: nonempty participant convention → empty user types are also permitted; reason: rank validity then cannot hold for r+1≥1, so this adds only the vacuous boundary case and retains every source instance
-- source:
--   Yang Bai, Xuan Guang, Lizhi Wang, STOC 2027 submission #1291 (October 2026), p. 14 (PDF p. 16); proof pp. 14–16 (PDF pp. 16–18), Theorem 6, equations (24)–(34)

import Mathlib
import Definitions.Def_NetworkSumSecure_Solvability_transformation

namespace NetworkSumSecure.Solvability

/-- Theorem 6, printed p.14 (PDF 16); the bound q>s+|W_r| uniformly
witnesses the sufficiently-large-field convention in its proof (34). -/
theorem theorem_6 {V E U F : Type} [Fintype V] [Fintype E] [Fintype U]
    [Field F] [Fintype F] (N : Network V E U) (r : ℕ)
    (hq : fieldThreshold (E := E) (U := U) r ≤ Fintype.card F)
    (z : U → ℕ) (C₀ : LocalCode N F z) (hRank : RankValid C₀ r) :
    ∃ (B : UserBlocks F z) (C : LocalCode N F z) (φ : Decoder N F),
      (∀ e, globalColumn C e = blockApply B (globalColumn C₀ e)) ∧
      Feasible C φ r := by sorry

end NetworkSumSecure.Solvability
