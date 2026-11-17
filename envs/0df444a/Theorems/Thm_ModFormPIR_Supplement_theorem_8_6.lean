-- Prove2me | Theorems.Thm_ModFormPIR_Supplement_theorem_8_6
-- name    : ModFormPIR.Supplement.theorem_8_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:49:26.196644+00:00
-- url     : https://prove2.me/theorems/938eb05f-1fda-4f7f-9267-02f988062b22
-- title:
--   Theorem 8.6 — every cone-delta function on $\mathbb Z_q^d$ has Fourier sparsity at least $q^{2\lfloor d/4\rfloor}$
-- statement:
--   Let $q$ be an odd prime and $\mathbb F$ any field with a primitive $q$-th root of unity $\gamma$. If there is a cone-delta function on $\mathbb Z_q^d$ over $\mathbb F$ with Fourier sparsity $k$, then
--
--   $$k\ge q^{2\lfloor d/4\rfloor}.$$
--
--   So a sparse cone-delta function, and by Lemma 4.4 any quadratic-phase delta expansion, has sparsity at least $q^{d/2-O(1)}$: the paper's approach cannot give a PIR exponent below $1/2$.
--
--   **Formalization Note** The cone-delta function is given by its Fourier coefficients $c=\hat f$ and its sparsity is the number of $w$ with $c(w)\neq0$ (`fourierSupport`). The statement is for every $d\in\mathbb N$ (for $d<4$ the bound is $1$).
--
--   Differences from the source:
--   - encoding: a cone-delta function f with Fourier sparsity k (|supp f̂|) → its Fourier coefficient family c = f̂ with IsConeDelta γ c, sparsity (fourierSupport c).card; reason: the Fourier representation is unique (Definition 4.1), so f and f̂ are the same data; Definition 2.1 is itself stated on the coefficients
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Theorem 8.6, p.32 (PDF p.36); Definitions 2.1, 4.1, pp.5, 19

import Mathlib
import Definitions.Def_ModFormPIR_Supplement_ConeDelta

set_option autoImplicit false

namespace ModFormPIR

namespace Supplement

/-- **Theorem 8.6**, p.32 (PDF p.36). Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval
from Modular Forms*, STOC 2027 submission (manuscript sha256 2442f3db…). Let `q` be an odd prime and `𝔽` any
field with a primitive `q`-th root of unity `γ`. Every cone-delta function on `ℤ_q^d` over `𝔽` has Fourier
sparsity `k ≥ q^{2⌊d/4⌋}`.

**Formalization Note.** The cone-delta function is given by its Fourier coefficients `c = f̂`
(Definitions 2.1, 4.1); its Fourier sparsity is the number of `w` with `c w ≠ 0`. Every `d ∈ ℕ` is allowed
(for `d < 4` the bound is `1`). `⌊d/4⌋` is natural-number division. -/
theorem theorem_8_6 (q : ℕ) [NeZero q] (hq : q.Prime) (hodd : Odd q) (𝔽 : Type*) [Field 𝔽] (γ : 𝔽)
    (hγ : IsPrimitiveRoot γ q) (d : ℕ) (c : (Fin d → ZMod q) → 𝔽) (hc : IsConeDelta γ c) :
    q ^ (2 * (d / 4)) ≤ (fourierSupport c).card := by sorry

end Supplement

end ModFormPIR
