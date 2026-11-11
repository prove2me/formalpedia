-- Prove2me | Theorems.Thm_OptAbstention_TLA_proposition_B_4
-- name    : OptAbstention.TLA.proposition_B_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:07:15.290532+00:00
-- url     : https://prove2.me/theorems/f803b687-dd01-4056-b4d9-3a97447d3da8
-- title:
--   Proposition B.4: the class $\mathcal F=\{(q\cdot\psi-t)_+-(-t)_+:\|q\|_1\le1\}$ has VC-subgraph dimension at most $Ck$
-- statement:
--   For $t\in\mathbb R$, $q\in\mathbb R^k$ let $\phi_{t,q}(x)=(q\cdot\psi(x)-t)_+-(-t)_+$ and $\mathcal F=\{\phi_{t,q}:t\in\mathbb R,\ q\in\mathbb R^k,\ \|q\|_1\le1\}$. There is a universal constant $C$ such that for every set $\Omega$, every $k\ge1$ and every $\psi:\Omega\to\mathbb R^k$,
--   $$\mathrm{VC}\text{-subgraph dimension of }\mathcal F\le Ck .$$
--   Together with the envelope $\|\psi(x)\|_\infty$ it feeds Fact A.6 in the proof of Proposition B.6. (The VC dimension of halfspaces in $\mathbb R^{k+1}$, published as `UnderstandingML.vcDim_halfspaces`, is a natural ingredient.)
--
--   Differences from the source:
--   - generalization: ψ measurable, in the setup of Lemma B.2 (with D, τ, δ) → every ψ: Ω → ℝ^k on any set Ω; D, τ, δ omitted; reason: the bound for every ψ contains the measurable case
--   - encoding: C a universal real constant → C a positive natural number; reason: a real bound on an integer-valued dimension is equivalent to its ceiling
-- source:
--   Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, Achieving the Optimal Abstention Rate for Learning with Distribution Shift, STOC 2027 submission (manuscript sha256 0fb30af1…), p. 39, Proposition B.4

import Mathlib
import Definitions.Def_OptAbstention_TLA_CappedReweighting

namespace OptAbstention.TLA

/-- Proposition B.4, p. 39: the VC-subgraph dimension of
`F = {ϕ_{t,q} : t ∈ ℝ, ‖q‖₁ ≤ 1}`, `ϕ_{t,q}(x) = (q · ψ(x) − t)_+ − (−t)_+`, is at most `C k`
with a universal constant `C`. -/
theorem proposition_B_4 : ∃ C : ℕ, 0 < C ∧
    ∀ {Ω : Type} (k : ℕ), 1 ≤ k → ∀ ψ : Ω → Fin k → ℝ,
      vcSubgraphDim (phiClass ψ) ≤ ((C * k : ℕ) : ℕ∞) := by sorry

end OptAbstention.TLA
