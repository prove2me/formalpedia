-- Prove2me | Theorems.Thm_NonMarkovColorings_Main_proposition_4_10
-- name    : NonMarkovColorings.Main.proposition_4_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:11:37.148145+00:00
-- url     : https://prove2.me/theorems/43f9fa50-af8a-44e3-8283-88c7457cb1cf
-- title:
--   Proposition 4.10 — the global coupling is valid: $F_{Y_0,X_0}\circ F_{X_0,Y_0}=\mathrm{id}$, so $F_{X_0,Y_0}$ is a bijection
-- statement:
--   For every pair $X_0,Y_0\in\widehat\Omega$ that differ at exactly one vertex,
--   $$F_{Y_0,X_0}\big(F_{X_0,Y_0}(\vec\sigma)\big)=\vec\sigma\quad\text{for every }\vec\sigma\in(V\times[k])^{T_{cp}},$$
--   and in particular $F_{X_0,Y_0}$ is a bijection of $(V\times[k])^{T_{cp}}$. Hence pairing $\vec\sigma$ with $F_{X_0,Y_0}(\vec\sigma)$ is a coupling of two copies of the dynamics; this is what makes the non-Markovian construction a legitimate $T_{cp}$-step coupling.
--
--   **Formalization Note.** Both $F$'s use the same four fixed orders; $F_{Y_0,X_0}$ runs its first chain from $Y_0$.
--
--   Differences from the source:
--   - generalization: standing assumptions of §3–5: Δ ≥ Δ0, k ≥ (1 + δ)Δ, C_cp large, one choice of the fixed orders → every graph with 7 ≤ egirth, every k, every C_cp ∈ ℕ, every choice of the four fixed orders; reason: §3.3–4.4 use only girth ≥ 7 and BC; the paper's setting is the special case
--   - encoding: F defined only when X0, Y0 differ at exactly one vertex → globalCoupling total; hypothesis (diffSet X0 Y0).card = 1; reason: the hypothesis is the paper's
-- source:
--   Jain, Mizgerd, Vigoda, Sampling Colorings Close to the Maximum Degree: Non-Markovian Coupling and Local Uniformity, arXiv:2604.11938 (PDF of 2026-11-03, sha256 f3bf0cf0…), p. 33, Proposition 4.10

import Mathlib
import Definitions.Def_NonMarkovColorings_Main_LabelingChain
import Definitions.Def_NonMarkovColorings_Main_BoundingChain
import Definitions.Def_NonMarkovColorings_Main_NonMarkovCoupling

namespace NonMarkovColorings.Main

/-- Proposition 4.10 (global coupling is valid). For labelings `X0, Y0` that differ at exactly
one vertex, `F_{Y0,X0}(F_{X0,Y0}(σ)) = σ` for every `σ ∈ (V × [k])^{T_cp}`; in particular
`F_{X0,Y0}` is a bijection. Stated for every graph of girth `≥ 7`, every `k`, every `C_cp` and
every choice of the fixed orders. -/
theorem proposition_4_10 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : 7 ≤ G.egirth) (k Ccp : ℕ) (o : Orders V) (X0 Y0 : V → Fin k)
    (hXY : (diffSet X0 Y0).card = 1) :
    (∀ σ : UpdSeq V k (Tcp V Ccp),
      globalCoupling G o Ccp Y0 X0 (globalCoupling G o Ccp X0 Y0 σ) = σ) ∧
    Function.Bijective (globalCoupling G o Ccp X0 Y0) := by sorry

end NonMarkovColorings.Main
