-- Prove2me | Theorems.Thm_ImpulseNMFG_Verification_approx_a_c
-- name    : ImpulseNMFG.Verification.approx_a_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:15:28.626838+00:00
-- url     : https://prove2.me/theorems/5b3a7568-0761-492c-bbb3-9b7af696d4a9
-- title:
--   Theorem 2.12, proof, (a)–(c), p. 10 — smooth approximations V_{i,m} of V_i with converging generators
-- statement:
--   Let $V_i$ satisfy conditions (ii) and (iii) of Theorem 2.12 for player $i$: $V_i\in C^2(W_i\setminus\partial D_i)\cap C^1(W_i)\cap C(\overline{W_i})$ with polynomial growth, $\partial D_i$ is a Lipschitz surface, and $V_i$ has locally bounded first and second derivatives near $\partial D_i$. Here $W_i=S\cap\bigcap_{j\ne i}D_j$ is the common waiting region, assumed open, and $\mathcal L$ is the generator of the diffusion. Then there is a sequence $(V_{i,m})_{m\in\mathbb N}$ such that
--
--   1. (a) $V_{i,m}\in C^2(W_i)\cap C^0(\overline{W_i})$ for each $m$;
--   2. (b) $V_{i,m}\to V_i$ uniformly on compact subsets of $\overline{W_i}$;
--   3. (c) $\{\mathcal LV_{i,m}\}_m$ is bounded on every compact subset of $W_i$, uniformly in $m$, and
--   $$
--   \mathcal LV_{i,m}\longrightarrow\mathcal LV_i\quad\text{uniformly on compact subsets of } W_i\setminus\partial D_i.
--   $$
--
--   This is the approximation step of the proof of Theorem 2.12, which the paper takes from Øksendal (proof of Thm. 10.4.1 and App. D). It lets Itô's formula, valid for the $C^2$ functions $V_{i,m}$, pass to $V_i$, which is only $C^1$ across $\partial D_i$.
--
--   **Formalization Note** The openness of $W_i$ is added: the page's $C^2(\cap_{j\ne i}D_j)$ and "locally bounded in $\cap_{j\ne i}D_j$" presuppose an open set, and in the proof $W_i$ is open because $S$ is open and each $A_j^*$ ($j\ne i$) is closed. "Locally bounded" is read as bounded on each compact subset of $W_i$, uniformly in $m$. The generator is the published `generator` with the game's $b$ and $\sigma$.
-- source:
--   Basei, Cao, Guo, Nonzero-sum stochastic games and mean-field games with impulse controls, arXiv:1901.08085v4, p. 10, Theorem 2.12, proof, (a)–(c)

import Mathlib
import Definitions.Def_ImpulseNMFG_Verification_Game
import Definitions.Def_ImpulseNMFG_Verification_QVI
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open ImpulseGames.Verification (State generator)

namespace ImpulseNMFG.Verification
noncomputable section
/-- Basei, Cao, Guo, Nonzero-sum stochastic games and mean-field games with impulse controls,
arXiv:1901.08085v4, p. 10, Theorem 2.12, proof, (a)–(c) (cited there from Øksendal,
proof of Thm. 10.4.1 and App. D).
Under (ii) and (iii) for player i there are functions V_{i,m}, m ∈ ℕ, with
(a) V_{i,m} ∈ C²(W_i) ∩ C⁰(cl W_i); (b) V_{i,m} → V_i uniformly on compact subsets of cl W_i;
(c) {𝓛V_{i,m}} is bounded on each compact subset of W_i uniformly in m, and
𝓛V_{i,m} → 𝓛V_i uniformly on compact subsets of W_i ∖ ∂D_i.
Here W_i = S ∩ ⋂_{j≠i} D_j is the common waiting region and 𝓛 is the published generator.
Formalization Note: the hypothesis that W_i is open is added. The page's C²(∩_{j≠i}D_j) and
"locally bounded in ∩_{j≠i}D_j" presuppose an open set; in the proof W_i is open because S is
open and each A*_j (j ≠ i) is closed, being an action region of an admissible profile.
"Locally bounded" is read as bounded on compact subsets of W_i, uniformly in m. -/
theorem approx_a_c {N d M : ℕ} [NeZero N] (G : Game N d M) (hG : G.Standing)
    (V : Fin N → State d → ℝ) (ξ : (i : Fin N) → State d → G.Imp i) (i : Fin N)
    (hii : Regular G V ξ i) (hiii : BoundaryRegular G V ξ i)
    (hW : IsOpen (commonWait G V ξ i)) :
    ∃ Vm : ℕ → State d → ℝ,
      (∀ m, ContDiffOn ℝ 2 (Vm m) (commonWait G V ξ i) ∧
        ContinuousOn (Vm m) (closure (commonWait G V ξ i))) ∧
      (∀ K ⊆ closure (commonWait G V ξ i), IsCompact K →
        TendstoUniformlyOn Vm (V i) atTop K) ∧
      (∀ K ⊆ commonWait G V ξ i, IsCompact K →
        ∃ B : ℝ, ∀ m, ∀ y ∈ K, |generator G.b G.σ (Vm m) y| ≤ B) ∧
      (∀ K ⊆ commonWait G V ξ i \ frontier (waitRegion G V ξ i), IsCompact K →
        TendstoUniformlyOn (fun m => generator G.b G.σ (Vm m))
          (generator G.b G.σ (V i)) atTop K) := by sorry
end
end ImpulseNMFG.Verification
