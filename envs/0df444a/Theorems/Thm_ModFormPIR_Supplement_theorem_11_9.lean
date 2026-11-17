-- Prove2me | Theorems.Thm_ModFormPIR_Supplement_theorem_11_9
-- name    : ModFormPIR.Supplement.theorem_11_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:49:58.362452+00:00
-- url     : https://prove2.me/theorems/94b180b4-3c62-4284-bdfd-fee609e3b30f
-- title:
--   Theorem 11.9 — a cone-delta function $\mathbb Z_q^d\to\mathbb Q(\zeta_q)$ with Fourier support in $S_d$, for every even lattice of determinant $\sqrt q$
-- statement:
--   Let $q$ be an odd prime and $\mathcal L\subseteq\mathbb R^r$ an even lattice of determinant $\sqrt q$. The group $\mathcal L^*/\mathcal L$ has order $q$, so it is cyclic; let $a+\mathcal L$ be a generator ($a\in\mathcal L^*$). Let $d>0$ and
--
--   $$S_d=\bigcup_{u\in\mathbb Z_q\setminus\{0\}}\Big\{z\in\mathbb Z_q^d:\sum_{i=1}^dw_{\mathcal L}(uz_ia)\le\frac{r(q+1)}{24}d\Big\},$$
--
--   where $w_{\mathcal L}$ is the coset cost (31). Then there is a cone-delta function $f:\mathbb Z_q^d\to\mathbb Q(\zeta_q)$, with $\gamma=\zeta_q$, such that $\hat f$ is supported on $S_d$.
--
--   With the bound $|S_d|\le q^{(\eta_{\mathcal L}+o(1))d}$ (Corollary 11.10) this gives the sparse cone-delta functions behind Main Theorem 5.3.
--
--   **Formalization Note** $\mathbb Q(\zeta_q)$ is `CyclotomicField q ℚ`; $f$ is given by its coefficients $c=\hat f$; the lattice is $B\mathbb Z^r$ with `IsEvenLatticeDetSqrt q B`, and $a$ is any element of $\mathcal L^*$ whose coset generates $\mathcal L^*/\mathcal L$.
--
--   Differences from the source:
--   - generalization: γ = ζ_q, the primitive root defining ℚ(ζ_q) → every primitive q-th root of unity γ of CyclotomicField q ℚ; reason: includes γ = ζ_q; it is equivalent to that case, since a field automorphism carrying ζ_q to γ maps a cone-delta function for ζ_q to one for γ with the same support
--   - encoding: a cone-delta function f : ℤ_q^d → ℚ(ζ_q) with f̂ supported on S_d → its Fourier coefficient family c = f̂ with IsConeDelta γ c; support: c w ≠ 0 → w ∈ S_d; reason: the Fourier representation is unique (Definition 4.1), so f and f̂ are the same data; Definition 2.1 is itself stated on the coefficients
--   - encoding: an even lattice ℒ ⊆ ℝ^r of determinant √q; a generator a + ℒ of ℒ*/ℒ; w_ℒ(u z_i a) → ℒ(B) = Bℤ^r with IsEvenLatticeDetSqrt q B; a : dual (lattice B) with IsCosetGenerator; latCost of the coset of (u z_i).val • a; reason: every lattice of Definition 11.1 is Bℤ^r; the coset of (u z_i).val • a does not depend on the representative since q a ∈ ℒ
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Theorem 11.9 with (32), p.53 (PDF p.57); Definitions 11.1–11.6, p.52 (PDF p.56)

import Mathlib
import Definitions.Def_ModFormPIR_Supplement_ConeDelta
import Definitions.Def_ModFormPIR_Supplement_Lattice

set_option autoImplicit false

namespace ModFormPIR

namespace Supplement

/-- **Theorem 11.9**, p.53 (PDF p.57), with (32). Henzinger, Ragavan, *Doubly-Efficient Private Information
Retrieval from Modular Forms*, STOC 2027 submission (manuscript sha256 2442f3db…). Let `q` be an odd prime,
`ℒ ⊆ ℝ^r` an even lattice of determinant `√q`, `a + ℒ` a generator of `ℒ*/ℒ`, and `d > 0`. Then there is a
cone-delta function `f : ℤ_q^d → ℚ(ζ_q)` with `f̂` supported on
`S_d = ⋃_{u ∈ ℤ_q ∖ {0}} {z : ∑_i w_ℒ(u z_i a) ≤ (r(q+1)/24) d}`.

**Formalization Note.** `ℚ(ζ_q)` is `CyclotomicField q ℚ` ("we use the notions of Section 4.2 over the field
`ℚ(ζ_q)`, with `γ = ζ_q`"). The statement is made for every primitive `q`-th root of unity `γ` of that field,
which includes `ζ_q` (and is equivalent to the case `γ = ζ_q`: a field automorphism carrying `ζ_q` to `γ`
carries a cone-delta function for `ζ_q` to one for `γ` with the same support). `f` is given by its Fourier
coefficients `c = f̂`. The lattice is `ℒ(B) = Bℤ^r`, `a ∈ ℒ*` any
generator, and `S_d` is `Sd q B a d`. -/
theorem theorem_11_9 (q : ℕ) [NeZero q] (hq : q.Prime) (hodd : Odd q) (r : ℕ)
    (B : Matrix (Fin r) (Fin r) ℝ) (hB : IsEvenLatticeDetSqrt q B) (a : ↥(dual (lattice B)))
    (ha : IsCosetGenerator B a) (d : ℕ) (hd : 0 < d) (γ : CyclotomicField q ℚ)
    (hγ : IsPrimitiveRoot γ q) :
    ∃ c : (Fin d → ZMod q) → CyclotomicField q ℚ, IsConeDelta γ c ∧
        ∀ w, c w ≠ 0 → w ∈ Sd q B a d := by sorry

end Supplement

end ModFormPIR
