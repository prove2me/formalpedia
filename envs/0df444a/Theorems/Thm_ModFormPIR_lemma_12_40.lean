-- Prove2me | Theorems.Thm_ModFormPIR_lemma_12_40
-- name    : ModFormPIR.lemma_12_40
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:03:07.590907+00:00
-- url     : https://prove2.me/theorems/be2ec77d-41ad-4e88-aa28-c024e315312e
-- title:
--   Lemma 12.40, p.78 — $\gamma d<2\ell_c+\vartheta(d-qm)$ at the selected cusps
-- statement:
--   Let $\beta$ satisfy (42)–(44), $a\in\mathbb Z_q$, and let $T\subseteq\mathbb Z_q^d$ be closed under units and under adding $b\mathbf 1$, with (45) at $a$ on $T$. Let $\vartheta\in[0,1]$ and let $\Gamma'$ be real with $\{z:\sum_iw_{q,\vartheta}(z_i)\le\Gamma'd\}\subseteq T$. Let $m$ be minimal with $A_m\not\equiv0$ and $g$ a lift of $g_{a,\lambda}$. Then
--   $$\Gamma'd<2\ell_g+\vartheta(d-qm).$$
--   In the printed case, $T=T_d(\vartheta,\nu)$, $\Gamma'=\gamma(\vartheta,\nu)$: for every selected cusp class $c$ one has $\gamma d<2\ell_c+\vartheta(d-qm)$.
--
--   With Lemmas 12.41 and 12.42 this is what contradicts the existence of the witness.
--
--   Differences from the source:
--   - generalization: the witness with (45) on T_d(ϑ,ν), budget γ(ϑ,ν) → any β with (42)–(44), any T closed under units and +b𝟏 with (45) at a on T, any real Γ′ with the edge sublevel set inside T; reason: the proof uses only these (with (u,b) = (1,0), (−1,1)), and T_d has them; the printed form would be vacuous by Theorem 12.2
--   - encoding: cusp c ∈ C with fixed lift → any a ∈ ℤ_q, any lift g of g_{a,λ}; reason: the statement is per class; §12.5.1 allows any fixed choice
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Lemma 12.40, p.78 (PDF p.82)

import Mathlib
import Definitions.Def_ModFormPIR_Witness

open scoped MatrixGroups

set_option autoImplicit false

namespace ModFormPIR

/-- **Lemma 12.40**, p.78. Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027 submission (manuscript sha256 2442f3db…).
For every selected cusp class `c`: `γd < 2ℓ_c + ϑ(d - qm)`.

**Formalization Note.** Printed for the witness with (45) on `T_d(ϑ,ν)`. Here `T` is any set closed under units and under `+b𝟏`, with (45) at `a` on `T` and `{z : ∑_i w_{q,ϑ}(z_i) ≤ Γ'd} ⊆ T`; the printed case is `T = T_d(ϑ,ν)`, `Γ' = γ(ϑ,ν)`. `m` is the Taylor order of `F`; `g` any lift of `g_{a,λ}`. -/
theorem lemma_12_40 (q d : ℕ) [Fact q.Prime] (hodd : Odd q) (hd : 1 ≤ d) (hqd : q ∣ d)
    (β : (Fin d → ZMod q) → ℂ) (hβ : IsNormalizedWitness β)
    (ρ : SL(2, ℤ) →* Matrix (ZMod q) (ZMod q) ℂ) (hρ : IsWeil q (muHalf q) ρ)
    (a : ZMod q) (T : Set (Fin d → ZMod q))
    (hTu : ∀ (u : (ZMod q)ˣ), ∀ z ∈ T, (fun i => (u : ZMod q) * z i) ∈ T)
    (hTs : ∀ z ∈ T, ∀ b : ZMod q, (fun i => z i + b) ∈ T)
    (h45 : IsOrthogonalOn β a T) (ϑ : ℝ) (h0 : 0 ≤ ϑ) (h1 : ϑ ≤ 1) (Γ' : ℝ)
    (hΓ : {z : Fin d → ZMod q | ∑ i, cost q ϑ (z i) ≤ Γ' * d} ⊆ T)
    (lam : ℕ) (g : SL(2, ℤ)) (hg : IsSelectedLift a lam g) (m : ℕ) (hm : IsTaylorOrder β m) :
    Γ' * d < 2 * ellG ρ β g + ϑ * ((d : ℝ) - (q : ℝ) * m) := by sorry

end ModFormPIR
