-- Prove2me | Theorems.Thm_ImpulseGames_Verification_verification_theorem
-- name    : ImpulseGames.Verification.verification_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:26:22.142185+00:00
-- url     : https://prove2.me/theorems/b2823bb9-6b5d-4158-8b22-a0a180b21736
-- title:
--   Theorem 3.3 — a regular solution of the QVI system (3.3) gives a Nash equilibrium with payoffs $V_1, V_2$
-- statement:
--   Consider the two-player impulse game of Section 2 under its standing assumptions. Let $V_1,V_2$ be real functions on $\bar S$ and suppose that (3.1) holds, i.e. for $i\in\{1,2\}$ there is a measurable $\delta_i:S\to Z_i$ with $\{\delta_i(x)\}=\arg\max_{\delta\in Z_i}\{V_i(\Gamma^i(x,\delta))+\phi_i(x,\delta)\}$ for each $x\in S$; assume moreover that $\delta_i$ is continuous on $S$. Set $\mathcal D_i=\{\mathcal M_iV_i-V_i<0\}$, and for $i\in\{1,2\}$ assume:
--
--   1. $V_i$ solves the QVI system (3.3a)–(3.3d);
--   2. $V_i\in C^2(\mathcal D_j\setminus\partial\mathcal D_i)\cap C^1(\mathcal D_j)\cap C(\bar S)$ and $V_i$ has polynomial growth;
--   3. $\partial\mathcal D_i$ is a Lipschitz surface and $V_i$ has locally bounded derivatives up to the second order in some neighbourhood of $\partial\mathcal D_i$;
--
--   Let $x\in S$ and assume $(\varphi_1^*,\varphi_2^*)\in\Phi_x$, where $\varphi_i^*=(\mathcal D_i,\delta_i)$. Then $(\varphi_1^*,\varphi_2^*)$ is a Nash equilibrium and
--   $$
--   V_i(x)=J^i(x;\varphi_1^*,\varphi_2^*),\qquad i\in\{1,2\}.
--   $$
--
--   This is the paper's main result: it turns the search for Nash equilibria of nonzero-sum impulse games into solving the system of quasi-variational inequalities (3.3), which Section 4 does explicitly for a one-dimensional game.
--
--   **Formalization Note.** One hypothesis is added to the page. Continuity of $\delta_i$ makes $\varphi_i^*$ a strategy in the sense of Definition 2.1, which asks $\xi_i$ to be continuous; the paper's Remark 3.6 relies on it to make $\mathcal D_i$ open. The fourth line of (3.3) is required on $\mathcal D_j\setminus\partial\mathcal D_i$, where $V_i$ is twice differentiable. The equality $V_i(x)=J^i$ is asserted for every admissible realization of $(\varphi_1^*,\varphi_2^*)$, and the Nash inequalities compare payoffs on every admissible realization. All conventions of the model are listed in the `Game` definition file.
-- source:
--   Aïd et al. (2020), Math. Oper. Res. 45(1), accepted manuscript, Theorem 3.3 (p. 9)

import Mathlib
import Definitions.Def_ImpulseGames_Verification_Game
import Definitions.Def_ImpulseGames_Verification_QVI

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ImpulseGames.Verification

/-- Theorem 3.3 (verification theorem): if `V_1, V_2` satisfy (3.1) with continuous `δ_i`, solve
the QVI system (3.3a)–(3.3d), satisfy the regularity conditions (ii)–(iii), `x ∈ S`, and `(φ_1^*, φ_2^*) = ((𝒟_1, δ_1), (𝒟_2, δ_2)) ∈ Φ_x`,
then `(φ_1^*, φ_2^*)` is a Nash equilibrium and `V_i(x) = J^i(x; φ_1^*, φ_2^*)` for `i = 1, 2`. -/
theorem verification_theorem {d k : ℕ} {Ω : Type*} [m : MeasurableSpace Ω]
    (P : Measure Ω) (𝔽 : Filtration ℝ≥0 m) (W : ℝ≥0 → Ω → (Fin k → ℝ))
    (hW : IsBrownianBasis P 𝔽 W) (G : Game d k) (hG : G.Standing)
    (V : Player → State d → ℝ) (δ : (i : Player) → State d → G.Imp i)
    (hV : VerificationHypotheses G V δ) (x : State d) (hx : x ∈ G.S)
    (hΦ : InPhi P 𝔽 W G x (starProfile G V δ)) :
    IsNash P 𝔽 W G x (starProfile G V δ) ∧
    ∀ Y : ℕ → ℝ≥0 → Ω → State d, IsAdmissible P 𝔽 W G x (starProfile G V δ) Y →
      ∀ i, V i x = payoff P G x (starProfile G V δ) Y i := by sorry

end ImpulseGames.Verification
