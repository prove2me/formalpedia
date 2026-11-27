-- Prove2me | Theorems.Thm_IncentiveFinNet_Supplement_theorem_8
-- name    : IncentiveFinNet.Supplement.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:35:10.441824+00:00
-- url     : https://prove2.me/theorems/958df4b7-cc11-4f18-93e1-418e5483e518
-- title:
--   Theorem 8 — risk aversion and expected returns are not identifiable from the network
-- statement:
--   Let $S=(\mu_i,\Sigma,\gamma_i)_{i\in[n]}$ and $S'=(\mu_i,\Sigma,\gamma'_i)_{i\in[n]}$ be two network settings with the same beliefs $M$ (column $i$ is $\mu_i$), the same shared covariance $\Sigma\succ0$, all edges allowed, and risk aversions $\gamma_i,\gamma'_i>0$; let $J=\{j\mid \gamma_j\ne\gamma'_j\}$. Then there is a setting $S^\dagger = (\mu_i^\dagger,\Sigma,\gamma_i)_{i\in[n]}$ with the risk aversions of $S$ and
--
--   $$
--   \mu^\dagger_i = \mu_i\quad\text{for all } i\notin J
--   $$
--
--   such that $S^\dagger$ and $S'$ have the same stable networks: a matrix $W$ is the network of a stable point of $S^\dagger$ if and only if it is the network of a stable point of $S'$.
--
--   An observer of the network therefore cannot tell whether a firm takes unusual positions because it is less risk averse or because it expects higher returns.
--
--   Differences from the source:
--
--   - reading: settings (µ_i, Σ, γ_i) written without Ψ_i → all edges allowed (sharedSetting); reason: Definition 1 (p.10): when all edges are allowed the Ψ_i = I_n terms are dropped
--   - reading: "the stable networks under S† and S′ are identical" → for every W, (∃ P, (W, P) stable under S†) ↔ (∃ P, (W, P) stable under S′); reason: the theorem compares networks, not prices
--   - encoding: µ_i = µ†_i for all i ∉ J → column i of M† equals column i of M whenever γ_i = γ′_i; reason: column i of M is µ_i; same condition
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, Theorem 8, p.25; restated and proved in A.16, pp.50–51

import Mathlib
import Definitions.Def_IncentiveFinNet_NetworkSetting
import Definitions.Def_IncentiveFinNet_Stable
import Definitions.Def_IncentiveFinNet_Supplement_sharedSetting

open Matrix

namespace IncentiveFinNet.Supplement

/-- **Theorem 8 (Non-identifiability of risk-aversion versus expected returns)**, Jalan,
Chakrabarti, Sarkar, arXiv:2212.06808v3, §4.2, p.25 (restated and proved in A.16, pp.50–51):
"Consider two network settings `S = (µ_i, Σ, γ_i)_{i∈[n]}` and `S′ = (µ_i, Σ, γ′_i)_{i∈[n]}` which
differ only in the risk-aversions of firms `J = {j | γ_j ≠ γ′_j} ⊆ [n]`. Then, there exists a
setting `S† = (µ†_i, Σ, γ_i)_{i∈[n]}` such that `µ_i = µ†_i` for all `i ∉ J` and the stable networks
under `S†` and `S′` are identical."

Stated for every `M` (columns `µ_i`), `Σ ≻ 0`, `γ, γ′ > 0`: there is `M†` (columns `µ†_i`) whose
column `i` equals that of `M` whenever `γ_i = γ′_i`, such that a matrix `W` is the network of a
stable point of `S† = (M†, Σ, γ)` iff it is the network of a stable point of `S′ = (M, Σ, γ′)`.

**Formalization Note**
* Settings written `(µ_i, Σ, γ_i)` without `Ψ_i` have all edges allowed (Definition 1, p.10); they
  are `sharedSetting`.
* "The stable networks are identical" compares the networks `W`, not the prices: the sets
  `{W | ∃ P, (W, P) stable}` coincide. -/
theorem theorem_8 {n : ℕ} (M Sig : Matrix (Fin n) (Fin n) ℝ) (hSig : Sig.PosDef)
    (γ γ' : Fin n → ℝ) (hγ : ∀ i, 0 < γ i) (hγ' : ∀ i, 0 < γ' i) :
    ∃ Mdag : Matrix (Fin n) (Fin n) ℝ, (∀ i, γ i = γ' i → ∀ k, Mdag k i = M k i) ∧
      ∀ W : Matrix (Fin n) (Fin n) ℝ,
        (∃ P, Stable (sharedSetting Mdag Sig γ hγ hSig) W P) ↔
          (∃ P, Stable (sharedSetting M Sig γ' hγ' hSig) W P) := by sorry

end IncentiveFinNet.Supplement
