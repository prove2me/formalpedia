-- Prove2me | Theorems.Thm_MayersQKD_trace_formulas
-- name    : MayersQKD.trace_formulas
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:46:59.567265+00:00
-- url     : https://prove2.me/theorems/a07e2799-2f50-4ea4-978c-03909ba3a272
-- title:
--   (9), (10), p.13 — the traces in the picture of $|\psi_{\alpha,\hat\theta}\rangle$
-- statement:
--   Fix an attack and a seed. For every outcome $(pass,\theta,R,\hat w)$,
--
--   $$
--   \mathrm{Tr}(\Pi_{(pass,\theta,R,\hat w)}\,\rho)=p(pass,\theta,R,\hat w)=8^{-n}\sum_\alpha\bigl\|M_{\hat w}\,P_{pass}[T_0\cap R,\delta n]\,|\psi_{\alpha,\hat\theta}\rangle\bigr\|^2
--   $$
--
--   and
--
--   $$
--   \mathrm{Tr}(P_0\,\Pi_{(pass,\theta,R,\hat w)}\,P_0\,\rho)=8^{-n}\sum_\alpha\bigl\|M_{\hat w}\,P_{pass}[T_0\cap R,\delta n]\,P_0\,|\psi_{\alpha,\hat\theta}\rangle\bigr\|^2 .
--   $$
--
--   These identities replace Alice's states in the bases $\theta$ by states in Bob's bases $\hat\theta$, where the test and $P_0$ are both diagonal.
--
--   Differences from the source:
--   - encoding: Tr on the joint classical and photon space → the block-diagonal formula prepTrace; reason: ρ and Π are block diagonal on the classical register, so the trace is that sum of blocks
--   - encoding: a fixed θ̂ (§6) → a fixed seed of the attack, which fixes θ̂; reason: the seed is the mixed-attack version of the same convention
--   - encoding: P₀ with c left implicit → an explicit c; reason: P₀ depends on E_c, hence on c
-- source:
--   Mayers, Quantum Key Distribution and String Oblivious Transfer in Noisy Channels, arXiv:quant-ph/9606003v1, §10, (9), (10), p.13

import Mathlib
import Definitions.Def_MayersBC_bb84State
import Definitions.Def_MayersQKD_T0
import Definitions.Def_MayersQKD_Attack
import Definitions.Def_MayersQKD_Lsub
import Definitions.Def_MayersQKD_testEffect

namespace MayersQKD

open MayersBC

/-- Mayers, arXiv:quant-ph/9606003v1, §10, (9), (10), p.13:
`Tr(Π ρ) = p(pass, θ, R, ŵ) = 8⁻ⁿ ∑_α ‖M_ŵ P_pass[T₀ ∩ R, δn] |ψ_{α,θ̂}⟩‖²` and
`Tr(P₀ Π P₀ ρ) = 8⁻ⁿ ∑_α ‖M_ŵ P_pass[T₀ ∩ R, δn] P₀ |ψ_{α,θ̂}⟩‖²`.

**Formalization Note.** `P_pass` is `P_j` of §7 with `j = pass`. Fixed seed; `P₀` depends on `c`
through `E_c`. -/
theorem trace_formulas {n r m : ℕ} (A : Attack n r m) (δ ε : ℝ) (s : A.Seed) (c pass : Bool)
    (θ : Bases n) (R : Finset (Fin n)) (what : Bits n) :
    prepTrace (testEffect A δ s pass θ R what) = (outcomeProb A δ s pass θ R what : ℂ) ∧
    outcomeProb A δ s pass θ R what =
      (1 / 8 : ℝ) ^ n * ∑ α : Bits n,
        ‖A.M s what (proj pass (A.commit s) what (T0 θ (A.commit s) ∩ R) (δ * n)
          (bb84State (A.commit s) α))‖ ^ 2 ∧
    prepTrace (fun w θ' => P0 A ε s what R θ c ∘ₗ testEffect A δ s pass θ R what w θ' ∘ₗ
        P0 A ε s what R θ c) =
      (((1 / 8 : ℝ) ^ n * ∑ α : Bits n,
        ‖A.M s what (proj pass (A.commit s) what (T0 θ (A.commit s) ∩ R) (δ * n)
          (P0 A ε s what R θ c (bb84State (A.commit s) α)))‖ ^ 2 : ℝ) : ℂ) := by sorry

end MayersQKD
