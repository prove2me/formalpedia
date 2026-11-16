-- Prove2me | Theorems.Thm_FourWayStream_ARHM_Supplement_residual_problem
-- name    : FourWayStream.ARHM.Supplement.residual_problem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:13:44.604806+00:00
-- url     : https://prove2.me/theorems/25066b90-e4c7-4811-ad4a-ab0e317424f1
-- title:
--   Lemma D.4 — the residual problem: $\mathrm{DHX}_{w,t}$ with advantage $1/(6w)$ gives $\mathrm{BHX}_{\lfloor w/100\rfloor,r}$, $r\ge t/512$, advantage $1/(8w)$
-- statement:
--   Let $w$ be large enough (at least a universal threshold $w_0$), $w'=\lfloor w/100\rfloor$ and $t\ge512\log_2w$. A $q$-qubit one-way protocol for $\mathrm{DHX}_{w,t}$ with success at least $\tfrac12+\tfrac1{6w}$ gives a $q$-qubit protocol for $\mathrm{BHX}_{w',r}$ with
--   $$r\ge t/512\qquad\text{and success at least}\qquad\frac12+\frac1{8w}.$$
--
--   This is the step from the graph problem of Assadi and Sundaresan to Block Hidden XOR; it keeps $\Omega(t)$ blocks for every $t\ge512\log w$, without assuming $t<w$.
--
--   **Formalization Note** "Gives a protocol" is the existence of a valid $\mathrm{BHX}_{w',r}$ protocol with message dimension at most $2^q$ for some integer $r\ge t/512$. Group $1$ is index $0$ of `Fin w`, which needs $w\ge1$ (an instance argument).
--
--   Differences from the source:
--   - encoding: a message of q qubits (classical information included) → a density matrix on C^d with d ≤ 2^q; reason: §4.3 defines q qubits as dimension at most 2^q; same protocols
--   - encoding: w large enough → w ≥ w₀ for a universal threshold w₀ quantified before t and the protocol; reason: the meaning of “large enough” in the proof (p.48)
--   - encoding: each edge of Multi-Block(X, Σ) assigned to Alice or Bob independently with probability 1/2 → a uniform ownership function on the pairs (layer step ℓ, endpoint in layer ℓ + 1), each indexing one edge; reason: every vertex of layer ℓ + 1 has exactly one edge from layer ℓ, so this is a bijection with the edges; same distribution
--   - encoding: [N], [m], [w], [r], [n], bits in {0,1}, edges {u, v} → Fin N, Fin m, Fin w, Fin r, Fin n (0-based), Bool, Sym2; reason: Lean convention; same instances
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), p.48, Lemma D.4 (proof pp.48–49)

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Supplement_NGC
import Definitions.Def_FourWayStream_ARHM_Supplement_BlockXOR

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM.Supplement

open QAlgorithms
open scoped Matrix

/-- Lemma D.4 (The residual problem), p.48. There is a width threshold `w₀` such that for every
`w ≥ w₀`, `w′ = ⌊w/100⌋` and every `t ≥ 512 log₂ w`: a `q`-qubit one-way protocol for `DHX_{w,t}` with
success at least `1/2 + 1/(6w)` gives a `q`-qubit protocol for `BHX_{w′,r}` with `r ≥ t/512` and
success at least `1/2 + 1/(8w)`. -/
theorem residual_problem :
    ∃ w₀ : ℕ, ∀ w t : ℕ, w₀ ≤ w → 512 * Real.logb 2 w ≤ t →
      ∀ [NeZero w] {nR : ℕ} (P : ShareProtocol (DHXV w t) nR), P.Valid →
        1 / 2 + 1 / (6 * (w : ℝ)) ≤ dhxSucc P → ∀ q : ℕ, P.d ≤ 2 ^ q →
        ∃ r : ℕ, (t : ℝ) / 512 ≤ r ∧ ∃ (nR' : ℕ) (P' : BHXProtocol (w / 100) r nR'),
          P'.Valid ∧ P'.d ≤ 2 ^ q ∧ 1 / 2 + 1 / (8 * (w : ℝ)) ≤ P'.succ := by sorry

end FourWayStream.ARHM.Supplement
