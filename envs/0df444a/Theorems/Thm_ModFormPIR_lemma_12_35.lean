-- Prove2me | Theorems.Thm_ModFormPIR_lemma_12_35
-- name    : ModFormPIR.lemma_12_35
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:02:26.676556+00:00
-- url     : https://prove2.me/theorems/9182a333-2790-4d5f-ac87-ace6f55fda6b
-- title:
--   Lemma 12.35, p.76 — $H_{c_{a,\lambda}}>\nu d$ at the selected cusps
-- statement:
--   Let $\beta$ satisfy (42)–(44), let $a\in\mathbb Z_q$, and let $T\subseteq\mathbb Z_q^d$ be closed under multiplication by units with (45) at $a$ on $T$, and $S^{\mathrm{sq}}_d(\nu')\subseteq T$. For $\lambda\in\{1,\dots,(q-1)/2\}$ and any lift $g\in SL_2(\mathbb Z)$ of $\begin{pmatrix}2a\lambda&-\lambda^{-1}\\\lambda&0\end{pmatrix}$,
--   $$H_g>\nu'd.$$
--   In the printed case, $T=T_d(\vartheta,\nu)$, $\nu'=\nu$: for every $a\in\mathcal A$ and $\lambda\in\{1,\dots,(q-1)/2\}$ one has $H_{c_{a,\lambda}}>\nu d$.
--
--   This is how the dual witness forces high vanishing at the selected cusps.
--
--   Differences from the source:
--   - generalization: the witness with (45) on T_d(ϑ,ν), budget ν → any β with (42)–(44), any unit-closed T with (45) at a on T, any real ν′ with S^sq_d(ν′) ⊆ T; reason: the proof uses only these, and T_d is unit-closed with S^sq_d(ν) ⊆ T_d; the printed form would be vacuous by Theorem 12.2
--   - encoding: a ∈ 𝒜, fixed lift g_{c_{a,λ}} → any a ∈ ℤ_q, any lift of g_{a,λ}; reason: the statement is per a; ρ(g) depends only on the reduction
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Lemma 12.35, p.76 (PDF p.80), with (50), p.75

import Mathlib
import Definitions.Def_ModFormPIR_Witness

open scoped MatrixGroups

set_option autoImplicit false

namespace ModFormPIR

/-- **Lemma 12.35**, p.76. Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027 submission (manuscript sha256 2442f3db…).
For every `a ∈ 𝒜` and `λ ∈ {1, …, (q-1)/2}`: `H_{c_{a,λ}} > νd`.

**Formalization Note.** Printed for the witness with (45) on `T_d(ϑ,ν)`. Here `T` is any set closed under coordinatewise multiplication by units, with (45) at `a` on `T` and `S^sq_d(ν') ⊆ T`; the printed case is `T = T_d(ϑ,ν)`, `ν' = ν`. `g` is any lift of
`g_{a,λ} = [2aλ, -λ⁻¹; λ, 0]`. -/
theorem lemma_12_35 (q d : ℕ) [Fact q.Prime] (hodd : Odd q) (hd : 1 ≤ d) (hqd : q ∣ d)
    (β : (Fin d → ZMod q) → ℂ) (hβ : IsNormalizedWitness β)
    (ρ : SL(2, ℤ) →* Matrix (ZMod q) (ZMod q) ℂ) (hρ : IsWeil q (muHalf q) ρ)
    (a : ZMod q) (T : Set (Fin d → ZMod q))
    (hTu : ∀ (u : (ZMod q)ˣ), ∀ z ∈ T, (fun i => (u : ZMod q) * z i) ∈ T)
    (h45 : IsOrthogonalOn β a T) (ν' : ℝ) (hν : Ssq q d ν' ⊆ T)
    (lam : ℕ) (g : SL(2, ℤ)) (hg : IsSelectedLift a lam g) :
    ν' * d < HG ρ β g := by sorry

end ModFormPIR
