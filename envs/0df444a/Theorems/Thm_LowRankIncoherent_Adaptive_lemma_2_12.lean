-- Prove2me | Theorems.Thm_LowRankIncoherent_Adaptive_lemma_2_12
-- name    : LowRankIncoherent.Adaptive.lemma_2_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:19:04.195688+00:00
-- url     : https://prove2.me/theorems/d2b552cc-4a2e-4864-8749-4879925ceed9
-- title:
--   Lemma 2.12 — complementary-channel formula and budgets
-- statement:
--   Let $E$ have Kraus rank exactly $r$ in the standing dimensions, with Kraus list $K_1,\ldots,K_r$. Fix a positive definite state $σ$ and $s>0$. Its complementary channel is $E^c(ρ)_{ij}=\operatorname{tr}(ρK_j^†K_i)$, with its Hilbert–Schmidt adjoint computed from that list. Then
--   $$H_s(σ)=(E^c)^†((E^c(σ)+sI_r)^{-1}),$$
--   and every state $ρ$ satisfies
--   $$\operatorname{tr}(ρH_s(σ))=\operatorname{tr}(E^c(ρ)(E^c(σ)+sI_r)^{-1}).$$
--   Writing $X$ for the purified-input output state,
--   $$\operatorname{tr}(σH_s(σ))=\operatorname{tr}f_s(X)≤r,\qquad0\preceq H_s(σ)\preceq s^{-1}I_a.$$
--   This gives both the complementary-channel identity and the trace and operator budgets used in adaptive input selection.
--
--   Differences from the source:
--   - encoding: finite complex registers and the source conventions → Fin-indexed matrices, explicit positivity and sample-count domains, and the operational definitions in this mission; reason: coordinate and domain conventions preserve every defined physical instance; no statistical guarantee is assumed
-- source:
--   Aadil Oufkir, Kean Chen, STOC 2027 submission #364 (October 2026), Lemma 2.12, printed p. 15 = PDF p. 15; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/364.pdf

import Definitions.Def_LowRankIncoherent_Adaptive_Algorithm

open Matrix MeasureTheory
open scoped MatrixOrder ComplexOrder ENNReal
noncomputable section

namespace LowRankIncoherent.Adaptive

theorem lemma_2_12 {a b r : ℕ} (ha : 0 < a) (hb : 2 ≤ b) (hrpos : 1 ≤ r)
    (hrmax : r ≤ a*b) (hfeasible : a ≤ r*b)
    (K : Fin r → Matrix (Fin b) (Fin a) ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1)
    (hrank : (choi (ChanTomoNB.krausMap K)).rank = r)
    (σ : Input a) (hσ : State σ) (hpd : σ.PosDef) (s : ℝ) (hs : 0 < s) :
    let E := ChanTomoNB.krausMap K
    let H := sensitivity E s σ
    H = complementAdj K (complement K σ + (s : ℂ) • 1)⁻¹ ∧
    (∀ ρ, State ρ → (ρ*H).trace =
      (complement K ρ * (complement K σ + (s : ℂ) • 1)⁻¹).trace) ∧
    rt (σ*H) = rt (fs s (outputState E σ)) ∧ rt (fs s (outputState E σ)) ≤ r ∧
    H.PosSemidef ∧ LE H ((s⁻¹ : ℂ) • 1) := by sorry

end LowRankIncoherent.Adaptive
