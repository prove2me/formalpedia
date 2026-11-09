-- Prove2me | Theorems.Thm_HopRamsey_lemma_1_eq_2
-- name    : HopRamsey.lemma_1_eq_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:45:15.333208+00:00
-- url     : https://prove2.me/theorems/7a87658e-9410-4574-b134-dfb7747a1ad3
-- title:
--   Eq. (2): the tape has an entry $\ge k$ with probability at most $L\delta^2/4\le\delta$
-- statement:
--   Assume $N=|V|\ge2$, $\Phi\ge2$ and $\varepsilon\in(0,1)$, with the parameters of Figure 2. Let $(\tau_{\ell,i})$, for $1\le\ell\le L$ and $1\le i\le\mu_{\ell-1}$, be independent geometric variables, $\tau_{\ell,i}$ with parameter $p_\ell$, and let $\Psi$ be the event that $\tau_{\ell,i}\ge k$ for some $(\ell,i)$. Then
--
--   $$
--   \sum_{\ell=1}^{L}\mu_{\ell-1}(1-p_\ell)^k\le\sum_{\ell=1}^{L}\mu_{\ell-1}e^{-p_\ell k}=L\cdot\frac{\delta^2}{4}\le\delta,
--   $$
--
--   and $\Pr[\Psi]\le\delta$.
--
--   This is the price of truncation: the tape process used in the analysis differs from the algorithm only on $\Psi$, which has probability at most $\delta$.
--
--   Differences from the source:
--   - encoding: the tape τ_{ℓ,i}, ℓ ∈ [1,L], i ∈ [1,µ_{ℓ−1}], of mutually independent geometric variables → `Measure.pi` over the index type Σ ℓ′ : Fin L, Fin µ_{ℓ′} (phase ℓ = ℓ′+1, so µ_{ℓ′} = µ_{ℓ−1} entries) of the geometric laws with parameter p_ℓ; reason: the same finite family of independent variables
--   - reading: the chain Pr[Ψ] ≤ Σ µ_{ℓ−1}(1−p_ℓ)^k ≤ Σ µ_{ℓ−1}e^{−p_ℓk} = ... = L·δ²/4 ≤ δ → its links as separate clauses: the first inequality of the sums, the equality with L·δ²/4, L·δ²/4 ≤ δ, and Pr[Ψ] ≤ δ; reason: the intermediate equalities are the proof; every displayed inequality between named quantities is stated
--   - reading: the standing assumptions of §4 (p.14) that enter the parameters: |V| ≥ n ≥ 2 (p.22), ε ∈ (0,1), Φ larger than a constant → hypotheses 2 ≤ P.N, 2 ≤ Φ, 0 < ε < 1 on the parameters of Figure 2; reason: these are the section's standing assumptions on the quantities this inequality involves (they give k ≥ 1, δ ≤ 1/2 and 0 < p_ℓ ≤ 1); the graph assumptions do not enter
--   - generalization: Φ = diam^{(h)}_G(V) → Φ is any real number ≥ 2 (it enters only through k); reason: the proof uses Φ only through the value of k; the paper's Φ = diam^{(h)}_G(V) is ≥ 2 under minimum weight 2 and |V| ≥ 2, so the statement specializes to it
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), proof of Lemma 1, eq. (2), p.20 (PDF p.22)

import Mathlib
import Definitions.Def_HopRamsey_Fig2Params
import Definitions.Def_HopRamsey_truncGeom

open scoped ENNReal

namespace HopRamsey

/-- Filtser, Zuzic, *Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with
Logarithmic Expected Distortion*, STOC 2027 submission (manuscript sha256 1ee73385…),
Eq. (2), proof of Lemma 1, p.20 (PDF p.22): "Let Ψ be the event that τ_{ℓ,i} ≥ k for some
ℓ ∈ [1,L] and i ∈ [1,µ_{ℓ−1}] (including tape entries that are never used). [...] As
Pr[τ_{ℓ,i} ≥ k] = (1 − p_ℓ)^k, by a union bound over the µ_{ℓ−1} tape entries of every phase ℓ, the
probability of this event is at most Pr[Ψ] ≤ Σ_{ℓ=L}^{1} µ_{ℓ−1}·(1 − p_ℓ)^k ≤
Σ_{ℓ=L}^{1} µ_{ℓ−1}·e^{−p_ℓ·k} = [...] = L·δ²/4 ≤ δ."

**Formalization Note.** The tape is indexed by `(ℓ', i)` with `ℓ' : Fin L` (phase `ℓ = ℓ' + 1`) and
`i : Fin µ_{ℓ−1}`; its entries are independent geometric variables with parameters `p_ℓ`
(`Measure.pi`). The conclusion has the numeric chain and the probability bound. Hypotheses: `|V| ≥ 2`,
`Φ ≥ 2`, `ε ∈ (0, 1)`, under which `0 < p_ℓ ≤ 1`. -/
theorem lemma_1_eq_2 (P : Fig2Params) (hN : 2 ≤ P.N) (hΦ : 2 ≤ P.Φ) (hε0 : 0 < P.ε)
    (hε1 : P.ε < 1) :
    (∑ ℓ ∈ Finset.Icc 1 P.L, (P.mu (ℓ - 1) : ℝ) * (1 - P.p ℓ) ^ P.k ≤
        ∑ ℓ ∈ Finset.Icc 1 P.L, (P.mu (ℓ - 1) : ℝ) * Real.exp (-(P.p ℓ * P.k))) ∧
    (∑ ℓ ∈ Finset.Icc 1 P.L, (P.mu (ℓ - 1) : ℝ) * Real.exp (-(P.p ℓ * P.k)) =
        P.L * P.delta ^ 2 / 4) ∧
    (P.L * P.delta ^ 2 / 4 ≤ P.delta) ∧
    (MeasureTheory.Measure.pi fun i : (Σ ℓ : Fin P.L, Fin (P.mu ℓ)) =>
        (geomLaw (P.p ((i.1 : ℕ) + 1))).toMeasure) {τ | ∃ i, P.k ≤ τ i} ≤
      ENNReal.ofReal P.delta := by sorry

end HopRamsey
