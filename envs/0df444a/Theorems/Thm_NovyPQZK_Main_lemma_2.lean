-- Prove2me | Theorems.Thm_NovyPQZK_Main_lemma_2
-- name    : NovyPQZK.Main.lemma_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:35:00.069062+00:00
-- url     : https://prove2.me/theorems/e3fc1445-1fbe-4807-afb9-9034e7340992
-- title:
--   Lemma 2 — the square-root success probability is Lipschitz in purified distance
-- statement:
--   Let $Q$ be a finite-dimensional register, $\Pi\in\operatorname{Proj}(Q)$ a projector and $\rho,\sigma\in D(Q)$ density matrices. Then
--
--   $$\Big|\sqrt{\operatorname{tr}(\Pi\rho)}-\sqrt{\operatorname{tr}(\Pi\sigma)}\Big|\le\mathrm{PD}(\rho,\sigma),$$
--
--   with $\mathrm{PD}(\rho,\sigma)=\sqrt{1-F^2(\rho,\sigma)}$ and $F$ the root fidelity. Compared with the trace-distance bound $|\operatorname{tr}(\Pi\rho)-\operatorname{tr}(\Pi\sigma)|\le\mathrm{PD}$, it tolerates a purified-distance error up to $\sqrt{\operatorname{tr}(\Pi\sigma)}$; the inverter analysis uses it to transfer success probabilities from an ideal state.
--
--   Differences from the source:
--   - encoding: register Q, Proj(Q), D(Q) (p. 14) → a finite basis type ι; IsProjector and IsDensity complex ι × ι matrices; F computed with the spectral square root; reason: finite-dimensional registers, the paper's setting
-- source:
--   Dupuis, Ligez, Medhioub, Salvail, Thibodeau, Post-Quantum Perfect Zero-Knowledge Arguments for NP From Any One-Way Permutation, arXiv:2610.33185 (sha256 857d8563…3257f), §3.1 p. 16, Lemma 2

import Mathlib
import Definitions.Def_NovyPQZK_Main_Fidelity

namespace NovyPQZK.Main

theorem lemma_2 {ι : Type} [Fintype ι] [DecidableEq ι] (P ρ σ : Matrix ι ι ℂ)
    (hP : IsProjector P) (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    |Real.sqrt (P * ρ).trace.re - Real.sqrt (P * σ).trace.re| ≤ purifiedDist ρ σ := by sorry

end NovyPQZK.Main
