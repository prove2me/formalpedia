-- Prove2me | Theorems.Thm_MarkovChainChoice_DimReduction_lemma_8
-- name    : MarkovChainChoice.DimReduction.lemma_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:07:48.270551+00:00
-- url     : https://prove2.me/theorems/1a5fe5b3-6832-46ca-ba36-20a1686cf234
-- title:
--   Lemma 8 — one step of Dimension Reduction stays in $\mathcal H$ and drops the minimizing product
-- statement:
--   Let $(\lambda,\rho)$ be a Markov chain choice model satisfying the standing assumptions and let $(\hat x,\hat z)\in\mathcal H$. Define $S_{\hat x}=\{j\in N:\hat x_j>0\}$, assume it is nonempty, and let
--   $$
--   \alpha_{\hat x}=\min\Big\{\frac{\hat x_j}{P_{j,S_{\hat x}}}: j\in S_{\hat x}\Big\},
--   $$
--   with $j_{\hat x}\in S_{\hat x}$ any index attaining this minimum. Assume $\alpha_{\hat x}<1$ and define
--   $$
--   \hat u_j=\frac{\hat x_j-\alpha_{\hat x}P_{j,S_{\hat x}}}{1-\alpha_{\hat x}},\qquad \hat v_j=\frac{\hat z_j-\alpha_{\hat x}R_{j,S_{\hat x}}}{1-\alpha_{\hat x}}\qquad (j\in N),
--   $$
--   and $S_{\hat u}=\{j\in N:\hat u_j>0\}$. Then $(\hat u,\hat v)\in\mathcal H$ and $S_{\hat u}\subseteq S_{\hat x}\setminus\{j_{\hat x}\}$.
--
--   Since $(\hat x,\hat z)=\alpha_{\hat x}(P_{S_{\hat x}},R_{S_{\hat x}})+(1-\alpha_{\hat x})(\hat u,\hat v)$, the lemma is the single step of the Dimension Reduction algorithm: it peels off one (Balance) solution and leaves a point of $\mathcal H$ with strictly smaller support.
--
--   **Formalization Note** The paper's $j_{\hat x}=\arg\min$ may not be unique; the statement holds for every minimizer. The paper writes $\subset$ for (not necessarily strict) inclusion; the conclusion uses $\subseteq$, and strictness is already carried by the removal of $j_{\hat x}$.
-- source:
--   Feldman, Topaloglu, Revenue Management Under the Markov Chain Choice Model, Oper. Res. 65(5), 2017, p. 1333, Lemma 8

import Mathlib
import Definitions.Def_MarkovChainChoice_Shared_Model
import Definitions.Def_MarkovChainChoice_Shared_Balance
import Definitions.Def_MarkovChainChoice_DimReduction_H
import Definitions.Def_MarkovChainChoice_DimReduction_Algorithm
open MarkovChainChoice.Shared

namespace MarkovChainChoice.DimReduction

theorem lemma_8 {n : ℕ} (M : Model n) (p : (Fin n → ℝ) × (Fin n → ℝ)) (hp : p ∈ H M)
    (hS : (drSupp p.1).Nonempty) (hα : drAlpha M p.1 < 1)
    (jbar : Fin n) (hjbar : jbar ∈ drSupp p.1)
    (hmin : p.1 jbar / purchase M (drSupp p.1) jbar = drAlpha M p.1) :
    drNext M p ∈ H M ∧ drSupp (drNext M p).1 ⊆ (drSupp p.1).erase jbar := by sorry

end MarkovChainChoice.DimReduction
