-- Prove2me | Theorems.Thm_NetworkedMarkets_Relaxation_proposition_1
-- name    : NetworkedMarkets.Relaxation.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:06.09102+00:00
-- url     : https://prove2.me/theorems/50dd92ce-af38-457d-bf51-7c6f4421a31a
-- title:
--   Proposition 1, p. 10 — for all feasible fees a competitive equilibrium exists, and all equilibria share supplies, demands and the trading sellers' prices
-- statement:
--   Consider a networked market satisfying the standing assumptions of §2 (positive masses $s_i,b_j$, disutilities $c_i\ge 0$, every type of degree at least one, and value distributions satisfying Assumption 1). Fix a commission-subscription pair $(\gamma,\mu)\in\Gamma\times\mathcal U$ and let $\mathcal X(\gamma,\mu)$ be the set of competitive equilibria $(p,x,q^s,q^b)$ of Definition 1. Then:
--
--   1. $\mathcal X(\gamma,\mu)\neq\emptyset$;
--   2. any two equilibria $(p,x,q^s,q^b),(p',x',q'^s,q'^b)\in\mathcal X(\gamma,\mu)$ have the same supply-demand vector,
--   $$q^s=q'^s,\qquad q^b=q'^b;$$
--   3. they have the same price for every seller type that trades: $p_i=p'_i$ whenever $q^s_i>0$.
--
--   Equilibria are thus essentially unique: only the flow and the prices of non-trading seller types can differ. This is what makes the platform's revenue under given fees well defined (Corollary 1).
--
--   **Formalization Note.** The statement holds for all of $\Gamma\times\mathcal U$, including $\gamma^s_i=1$. Assumption 2 is not assumed (the paper states Proposition 1 before introducing it).
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), p. 10, Proposition 1

import Mathlib
import Definitions.Def_NetworkedMarkets_Relaxation_Setting

open Filter Topology

namespace NetworkedMarkets.Relaxation

theorem proposition_1 {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (M : Market S B) (hM : M.Standing1)
    (f : Fees S B) (hf : f.InGammaU) :
    (∃ (p : S → ℝ) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ), M.IsCE f p x qs qb) ∧
    ∀ (p : S → ℝ) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ)
      (p' : S → ℝ) (x' : S → B → ℝ) (qs' : S → ℝ) (qb' : B → ℝ),
      M.IsCE f p x qs qb → M.IsCE f p' x' qs' qb' →
        qs = qs' ∧ qb = qb' ∧ ∀ i, 0 < qs i → p i = p' i := by sorry

end NetworkedMarkets.Relaxation
