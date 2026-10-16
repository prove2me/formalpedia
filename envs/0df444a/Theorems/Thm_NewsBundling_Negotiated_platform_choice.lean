-- Prove2me | Theorems.Thm_NewsBundling_Negotiated_platform_choice
-- name    : NewsBundling.Negotiated.platform_choice
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T02:43:50.837348+00:00
-- url     : https://prove2.me/theorems/b87a59cc-bc65-49c6-9819-a990bcb51801
-- title:
--   §6, p. 19 — in the negotiated game the platform sets λ = min{q, Λ} for every q < 1
-- statement:
--   Assume $\tfrac13<\beta\le1$, $c>2\beta$ and $0<\Lambda<\tfrac12$. In every subgame-perfect equilibrium of the negotiated content-bundling game, the platform's share of news at quality $q$ is
--
--   $$\lambda(q)=\min\{q,\Lambda\}\qquad\text{for every } q\in[0,1).$$
--
--   Since the platform keeps all advertising revenue ($\varphi_0=1$), it maximizes the time $T_0$ consumers spend on its site; for $q\le\Lambda$ every $\lambda\in[q,\Lambda]$ gives $T_0=1$ and the tie-break picks $\lambda=q$, while for $q>\Lambda$ the cap $\lambda=\Lambda$ is the unique maximizer. This is the platform's stage of the backward induction that leads to the fee formulas (4) and (6).
--
--   **Formalization Note** The statement excludes $q=1$: there $T_0=0$ for every $\lambda$, and the paper's tie-break ("it chooses the smallest one") selects $\lambda=0\ne\min\{1,\Lambda\}$.
-- source:
--   de Cornière & Sarvary, Social Media and News: Content Bundling and News Quality, TSE Working Paper n° 1152 (August 2021), p. 19, §6, Equilibrium, second paragraph; tie-break p. 19, second paragraph of §6

import Mathlib
import Definitions.Def_NewsBundling_Negotiated_Setting

namespace NewsBundling.Negotiated

theorem platform_choice (β c Λ : ℝ) (hN : NegAssumptions β c Λ) :
    ∀ σ, IsNegotiatedSPE β c Λ σ → ∀ q ∈ Set.Ico (0 : ℝ) 1, σ.platform q = min q Λ := by sorry

end NewsBundling.Negotiated
