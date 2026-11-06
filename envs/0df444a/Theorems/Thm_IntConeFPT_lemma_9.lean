-- Prove2me | Theorems.Thm_IntConeFPT_lemma_9
-- name    : IntConeFPT.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:44:08.801681+00:00
-- url     : https://prove2.me/theorems/bffe7336-e8c2-4789-b215-fa6c36e8126b
-- title:
--   Lemma 9 (One-Type Soundness and Completeness) — for $\tau=1$, budget $\gamma$ is attainable iff some $\hat K_R(\gamma)$ has an integer point
-- statement:
--   Let $I$ be a valid instance with $\tau=1$, $N_{\max}\in\mathbb Z_{\ge0}$ and $\gamma\in\mathbb Q$. Then (♣) subject to (1.1) has a feasible solution $\lambda$ with $\mathrm{cost}(\lambda)\le\gamma$ if and only if there is a set $R\subseteq\{0,\dots,2^d-1\}^d$ with $|R|\le2^d$ such that
--   $$
--   \hat K_R(\gamma)\cap\mathbb Z^{(d+1)|R|}\ne\emptyset .
--   $$
--   This is the correctness of the residue-class formulation for one type.
--
--   **Formalization Note** $K_R(\gamma)$ and $\hat K_R(\gamma)$ are `K` and `Khat`; an integer point has integral $z$ and $n$ blocks (`IsIntegral`).
--
--   Differences from the source:
--   - encoding: a set R ⊆ {0, …, 2^d − 1}^d with |R| ≤ 2^d → a duplicate-free list of length ≤ 2^d (IsCandidate); reason: a finite set given by a listing; only the set matters
--   - encoding: the budget sum (3.2e) of finite reals → sum in EReal; reason: each summand is finite under (3.2b) for a valid instance
--   - encoding: P = P^(1), f = f^(1) with τ = 1 → I.P t, I.f t for t : Fin I.τ, with hτ : I.τ = 1; reason: Lean convention; same instance
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint, sha256 9e28aed8…bc08a), Lemma 9, p.12

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

/-- **Lemma 9 (One-Type Soundness and Completeness).**
Jansen–Ohnesorge–Schumacher, *A Constructive FPT Algorithm for Integer Cone Optimization with
Convex Costs*, arXiv:2609.31328 (preprint), Lemma 9, p.12: "Suppose τ = 1, and write P = P^(1),
S = P ∩ (Z^d × R^k), f = f^(1), K_R(γ) = K_(R)(γ), and K̂_R(γ) = K̂_(R)(γ). The problem (♣) subject
to (1.1) has a feasible solution with cost at most γ if and only if there is a set
R ⊆ {0, …, 2^d − 1}^d with |R| ≤ 2^d such that K̂_R(γ) ∩ Z^{(d+1)|R|} ≠ ∅."

**Formalization Note.** `γ` is a rational budget (p.12) and `N_max ∈ Z≥0`. A set `R` is a
duplicate-free list of residues (`IsCandidate`). -/
theorem lemma_9 (I : Instance) (hI : I.Valid) (hτ : I.τ = 1) (Nmax : ℕ) (γ : ℚ) :
    (∃ μ, I.FeasibleN Nmax μ ∧ I.cost μ ≤ γ) ↔
      ∃ R : Cand I, IsCandidate I R ∧ ∃ zn ∈ Khat I R Nmax γ, IsIntegral zn := by sorry

end IntConeFPT
