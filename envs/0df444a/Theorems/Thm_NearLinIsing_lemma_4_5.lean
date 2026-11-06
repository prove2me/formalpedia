-- Prove2me | Theorems.Thm_NearLinIsing_lemma_4_5
-- name    : NearLinIsing.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:43:45.205661+00:00
-- url     : https://prove2.me/theorems/a7d9e458-baf0-4497-9b73-2f814c10acab
-- title:
--   Lemma 4.5 — recovery of Ising spins
-- statement:
--   There is an absolute constant $C_5>0$ such that, for every well-formed graph $G$ with edge activities $\beta_e\ge1$ and $t_e=(\beta_e-1)/(\beta_e+1)$, the following holds for the concrete recovery map, which adds each missing edge $e$ independently with probability $t_e$ and then assigns an independent fair sign to each connected component. Let $\mathcal K(F,\sigma)$ be the probability that the input $F$ gives output $\sigma$. Then:
--
--   1. the output events and the cost are measurable;
--   2. $\sum_F\pi_2(F)\,\mathcal K(F,\sigma)=\mu_{\mathrm{Ising}}(\sigma)$ for the even-subgraph law (6), so the resulting spins have law $\mu_{\mathrm{Ising}}$;
--   3. the map contracts total variation: $d_{TV}(\rho\mathcal K,\pi\mathcal K)\le d_{TV}(\rho,\pi)$ for all laws $\rho,\pi$ on edge sets;
--   4. its expected work is at most $C_5(1+n+m)$ for every input.
--
--   This step converts a sample of the even-subgraph law into a sample of the Ising law.
--
--   Differences from the source:
--   - generalization: O(m) work, under §2.6: no isolated vertices, so m ≥ 1 and n ≤ 2m → C₅(1 + n + m) for every graph; reason: under the standing convention this is at most 4C₅m; the 1 pays the constant overhead on the empty graph
--   - encoding: the recovery map → the concrete charged program `recoverSpins`, with measurability of output and cost as a clause; reason: the map of the lemma, in the machine of §2.6
--   - encoding: a graph G with edge activities β_e ≥ 1 → a well-formed `IncGraph` G and β : Fin m → ℝ with 1 ≤ β e; reason: the input format of §2.6 (simple graph, indexed incidence lists)
-- source:
--   Miao, Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness Threshold, arXiv:2611.04786, Lemma 4.5 and its proof, p. 21; Eq. (6), p. 8

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_NearLinIsing_recover

open MeasureTheory
open scoped ENNReal

namespace NearLinIsing

/-- **Lemma 4.5** (Recovery of Ising spins), p. 21.

Miao, *Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness
Threshold*, arXiv:2611.04786, Lemma 4.5 and its proof, p. 21; even-subgraph law (6), p. 8.

There is an absolute constant `C₅ > 0` such that, for every well-formed `G` and edge activities
`β_e ≥ 1`, with `t_e = (β_e − 1)/(β_e + 1)`, the concrete recovery `recoverSpins` (add each missing
edge `e` independently with probability `t_e`, then give each connected component an independent
fair sign), with recovery kernel `K(F, σ) = P(output σ | input F)`, satisfies:
1. its output events and its cost are measurable;
2. applied to the even-subgraph law (6), its output has law `µ_Ising` with activities `β_e`:
   `∑_F π₂(F) K(F, σ) = µ_Ising(σ)`;
3. it contracts total variation: `d_TV(ρK, πK) ≤ d_TV(ρ, π)` for all laws `ρ`, `π` of edge sets;
4. its expected work is at most `C₅ (1 + n + m)` for every input `F`.

**Formalization Note.** The paper's `O(m)` work is under the standing convention of §2.6 that
isolated vertices are removed first, so `m ≥ 1` and `n ≤ 2m`; the bound `C₅ (1 + n + m)` holds for
every graph (the `1` pays the constant overhead on the empty graph) and gives `4 C₅ m` under that
convention. -/
theorem lemma_4_5 :
    ∃ C₅ : ℝ, 0 < C₅ ∧
    ∀ G : IncGraph, G.WellFormed → ∀ β : Fin G.m → ℝ, (∀ e, 1 ≤ β e) →
      (∀ F : Finset (Fin G.m), ∀ σ : Fin G.n → Bool,
        MeasurableSet {τ : Tape | spinsOf G (runVal (recoverSpins G
          (fun e => if h : e < G.m then (β ⟨e, h⟩ - 1) / (β ⟨e, h⟩ + 1) else 0) (encF G F)) τ) = σ}) ∧
      (∀ F : Finset (Fin G.m), Measurable (fun τ : Tape => runCost (recoverSpins G
          (fun e => if h : e < G.m then (β ⟨e, h⟩ - 1) / (β ⟨e, h⟩ + 1) else 0) (encF G F)) τ)) ∧
      (∀ σ : Fin G.n → Bool,
        ∑ F : Finset (Fin G.m), G.evenLaw (fun e => (β e - 1) / (β e + 1)) F *
          tapeLaw.real {τ : Tape | spinsOf G (runVal (recoverSpins G
            (fun e => if h : e < G.m then (β ⟨e, h⟩ - 1) / (β ⟨e, h⟩ + 1) else 0) (encF G F)) τ) = σ}
          = G.isingLawGen β σ) ∧
      (∀ ρ π : Finset (Fin G.m) → ℝ, (∀ F, 0 ≤ ρ F) → ∑ F, ρ F = 1 → (∀ F, 0 ≤ π F) →
        ∑ F, π F = 1 →
        MarkovMixing.tvDist
          (fun σ => ∑ F, ρ F * tapeLaw.real {τ : Tape | spinsOf G (runVal (recoverSpins G
            (fun e => if h : e < G.m then (β ⟨e, h⟩ - 1) / (β ⟨e, h⟩ + 1) else 0) (encF G F)) τ) = σ})
          (fun σ => ∑ F, π F * tapeLaw.real {τ : Tape | spinsOf G (runVal (recoverSpins G
            (fun e => if h : e < G.m then (β ⟨e, h⟩ - 1) / (β ⟨e, h⟩ + 1) else 0) (encF G F)) τ) = σ})
          ≤ MarkovMixing.tvDist ρ π) ∧
      (∀ F : Finset (Fin G.m),
        ∫⁻ τ, (runCost (recoverSpins G
            (fun e => if h : e < G.m then (β ⟨e, h⟩ - 1) / (β ⟨e, h⟩ + 1) else 0) (encF G F)) τ : ℝ≥0∞)
          ∂tapeLaw ≤ ENNReal.ofReal (C₅ * (1 + (G.n : ℝ) + G.m))) := by sorry

end NearLinIsing
