-- Prove2me | Theorems.Thm_GaussLocalMaxColoring_Main_lemma_38
-- name    : GaussLocalMaxColoring.Main.lemma_38
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:23:44.106206+00:00
-- url     : https://prove2.me/theorems/9c152663-d06a-4fc1-a856-b385301c74b8
-- title:
--   Lemma 38 — under the band bounds, $\mathbb P_g[\mathcal G_i(r)]\le(i+2)\varepsilon_t$ and $\mathbb P_g[\mathcal L_i(r)]\le(i+2)\varepsilon_t$ for $0\le i\le m_0=o(\ell)$
-- statement:
--   $m_0=o(\ell)$, and: for every constant $K_{\mathcal P}$ and $n$ sufficiently large, in the Section 5 setting under the analysis convention (exact edge constraint, $\Gamma_{rx}(X)\succeq0$ for every edge $rx$), for every band partition $\mathcal P$ with $|\mathcal P|\le K_{\mathcal P}\log n+K_{\mathcal P}$ and every nested core sequence $V=F_0\supseteq F_1\supseteq\cdots$: if $|S_{r,P}|\le\exp((C_D(\rho)+\eta)t^2/2)$ for every $r\in V$, $P\in\mathcal P$, $\rho\in P$, and $p_{F_{j-1}}(x)\le e^{-t^2/2}$ for every $1\le j\le\ell$ and $x\in F_j$, then for every $0\le i\le m_0$ and every vertex $r$,
--   $$\mathbb P_g[\mathcal G_i(r)]\le(i+2)\varepsilon_t\quad\text{and}\quad\mathbb P_g[\mathcal L_i(r)]\le(i+2)\varepsilon_t.$$
--
--   Differences from the source:
--   - generalization: the cores F₀ ⊇ ⋯ ⊇ F_ℓ produced by Algorithm 2 → any ℕ-indexed nested sequence F with F 0 = V; reason: the lemma's proof uses only the stated hypotheses on the cores; Algorithm 2's cores extended by F_j = F_ℓ for j > ℓ are an instance
--   - generalization: the fixed partition 𝒫 of §5.2 with O(log n) intervals → every band partition with |𝒫| ≤ K_𝒫 log n + K_𝒫, for every constant K_𝒫 (N₀ depends on K_𝒫); reason: covers the paper's partition whatever its O(log n) constant
--   - reading: "for sufficiently large n, m₀ = o(ℓ), and …" → m₀(n)/ℓ(n) → 0, and ∃ N₀ (after K_𝒫, before everything else) with the bounds for n ≥ N₀; reason: the paper's uniform asymptotic convention
--   - encoding: §5 analysis convention (p. 35): edge constraint and Γ_rx(X) ⪰ 0 treated as exact → ExactSDPVectors G v and Γ_rx(gram v) ⪰ 0 for every edge rx as hypotheses; reason: the lemma is proved under this convention (Lemma 42 (ii) needs Γ ⪰ 0)
--   - encoding: §5 standing assumptions (G 3-colorable, every degree ≤ n^β, β = 0.692601; Table 3 parameters as functions of n) → binders G.Colorable 3, maxDegOn G univ ≤ n^beta5, and the Table 3 definitions of the Section5 module; reason: the section states them once (pp. 31, 35); they are hypotheses of every §5 lemma
--   - encoding: vertex set V with a fixed total order breaking ties → V = Fin n with its order; reason: Lean convention; every finite ordered vertex set is relabelled this way
--   - encoding: vectors in R^d, g ∼ N(0, I_d), P_g → Space d = EuclideanSpace ℝ (Fin d), any d, Mathlib stdGaussian (gaussProb); reason: Lean convention; same instances
-- source:
--   Deguchi, Kawarabayashi, Yoneda, Yoneda (2026), An O(n^0.1537)-Coloring Algorithm for 3-Colorable Graphs, arXiv:2610.35859 (SHA-256 9917b0a1…), Lemma 38, printed p. 40 (PDF 42); proof pp. 46–47 (PDF 48–49)

import Mathlib
import Definitions.Def_GaussLocalMaxColoring_Main_Bands

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main
open Classical

namespace GaussLocalMaxColoring.Main

/-- **Lemma 38** (p. 40, PDF 42). `m₀ = o(ℓ)`, and: for every constant `K_𝒫` (the `O(log n)`
bound on `|𝒫|`) and `n` sufficiently large, in the Section 5 setting (analysis convention: exact
edge constraint and `Γ_rx(X) ⪰ 0` for every edge `rx`), for every band partition `𝒫` with
`|𝒫| ≤ K_𝒫 log n + K_𝒫` and every nested core sequence `V = F₀ ⊇ F₁ ⊇ ⋯`: if
`|S_{r,P}| ≤ exp((C_D(ρ) + η)t²/2)` for every `r ∈ V`, `P ∈ 𝒫`, `ρ ∈ P`, and
`p_{F_{j−1}}(x) ≤ e^{−t²/2}` for every `1 ≤ j ≤ ℓ` and `x ∈ F_j`, then
`P_g[𝒢_i(r)] ≤ (i+2)ε_t` and `P_g[ℒ_i(r)] ≤ (i+2)ε_t` for every `0 ≤ i ≤ m₀` and every `r ∈ V`. -/
theorem lemma_38 :
    IsLittleO1 (fun n => (m0 n : ℝ) / numLevels n) ∧
    ∀ KP : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∀ (d : ℕ) (G : SimpleGraph (Fin n)), G.Colorable 3 →
      (maxDegOn G Finset.univ : ℝ) ≤ (n : ℝ) ^ beta5 →
      ∀ v : Fin n → Space d, ExactSDPVectors G v →
      (∀ r x, G.Adj r x → (Gamma G (gram v) r x).PosSemidef) →
      ∀ Pt : Finset Ival, IsBandPartition n Pt → (Pt.card : ℝ) ≤ KP * Real.log n + KP →
      ∀ F : ℕ → Finset (Fin n), F 0 = Finset.univ → (∀ i, F (i + 1) ⊆ F i) →
      (∀ r, ∀ P ∈ Pt, ∀ ρ ∈ P.toSet,
        ((band (gram v) r P).card : ℝ) ≤ Real.exp ((capacity D5 ρ + eta5) * t5 n ^ 2 / 2)) →
      (∀ j, 1 ≤ j → j ≤ numLevels n → ∀ x ∈ F j,
        pLocal G v (F (j - 1)) x ≤ Real.exp (-(t5 n ^ 2 / 2))) →
      ∀ i, i ≤ m0 n → ∀ r : Fin n,
        gaussProb (globalEvent v F r i) ≤ (i + 2) * epsT n ∧
          gaussProb (localEvent G v F r i) ≤ (i + 2) * epsT n := by sorry

end GaussLocalMaxColoring.Main
