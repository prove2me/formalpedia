-- Prove2me | Theorems.Thm_IntConeFPT_corollary_10
-- name    : IntConeFPT.corollary_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:44:19.744223+00:00
-- url     : https://prove2.me/theorems/04ad966c-0963-45b3-b1d7-507cdc83441e
-- title:
--   Corollary 10 (Soundness and Completeness for Multiple Types) — budget $\gamma$ attainable iff some candidate $\hat K_R(\gamma)$ has an integer point
-- statement:
--   Let $I$ be a valid instance, $N_{\max}\in\mathbb Z_{\ge0}$ and $\gamma\in\mathbb Q$. Then (♣) subject to (1.1) has a feasible solution with cost at most $\gamma$ if and only if some candidate tuple $R$ ($|R^{(t)}|\le2^d$ for every $t$) satisfies
--   $$
--   \hat K_R(\gamma)\cap\mathbb Z^{D_R}\ne\emptyset,\qquad D_R=(d+1)\sum_t|R^{(t)}|.
--   $$
--   Proposition 14 searches over budgets and candidate tuples using this equivalence.
--
--   **Formalization Note** $K_R(\gamma)$ and $\hat K_R(\gamma)$ are `K` and `Khat`; an integer point has integral $z$ and $n$ blocks (`IsIntegral`).
--
--   Differences from the source:
--   - encoding: candidate tuple R = (R^(1), …, R^(τ)) with |R^(t)| ≤ 2^d → R : Fin τ → List residues, each duplicate-free of length ≤ 2^d (IsCandidate); reason: a finite set given by a listing; only the sets matter
--   - encoding: the budget sum (3.2e) of finite reals → sum in EReal; reason: each summand is finite under (3.2b) for a valid instance
--   - encoding: types t ∈ [τ] = {1, …, τ} → t : Fin τ (0-based); reason: Lean convention; same instances
--   - reading: P^(1), …, P^(τ) (implicitly at least one type) → Instance.Valid requires 1 ≤ τ; reason: the paper lists τ types and its bounds contain log(τ + 1); there are no instances with τ = 0 in the source
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint, sha256 9e28aed8…bc08a), Corollary 10, p.13

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encInt
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_OnlineCRS_Combine_encVec
import Definitions.Def_IntConeFPT_Instance
import Definitions.Def_IntConeFPT_Problem
import Definitions.Def_IntConeFPT_Residue
import Definitions.Def_IntConeFPT_Formulation

open OnlineCRS.Combine

namespace IntConeFPT

/-- **Corollary 10 (Soundness and Completeness for Multiple Types).**
Jansen–Ohnesorge–Schumacher, *A Constructive FPT Algorithm for Integer Cone Optimization with
Convex Costs*, arXiv:2609.31328 (preprint), Corollary 10, p.13: "The problem (♣) subject to (1.1) has a
feasible solution with cost at most γ if and only if some candidate tuple R satisfies
K̂_R(γ) ∩ Z^{D_R} ≠ ∅."

**Formalization Note.** A candidate tuple has `|R^(t)| ≤ 2^d` for every type (Corollary 8); each
`R^(t)` is a duplicate-free list. `γ` is a rational budget and `N_max ∈ Z≥0`. -/
theorem corollary_10 (I : Instance) (hI : I.Valid) (Nmax : ℕ) (γ : ℚ) :
    (∃ μ, I.FeasibleN Nmax μ ∧ I.cost μ ≤ γ) ↔
      ∃ R : Cand I, IsCandidate I R ∧ ∃ zn ∈ Khat I R Nmax γ, IsIntegral zn := by sorry

end IntConeFPT
