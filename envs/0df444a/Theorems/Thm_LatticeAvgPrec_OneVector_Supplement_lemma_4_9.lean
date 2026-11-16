-- Prove2me | Theorems.Thm_LatticeAvgPrec_OneVector_Supplement_lemma_4_9
-- name    : LatticeAvgPrec.OneVector.Supplement.lemma_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:40:52.539199+00:00
-- url     : https://prove2.me/theorems/d543221d-dd5d-47fe-a434-22bb99c06517
-- title:
--   Lemma 4.9 — A small integer shear
-- statement:
--   Fix an available matrix-multiplication exponent $2<\omega\le3$. There are a program $\mathcal P$ of the logarithmic-cost RAM with coin flips, an exponent $c$ and a subpolynomial factor $g$ such that the following holds for all $q,r'\ge0$ with $q+r'\ge1$ and every $h\ge1$.
--
--   Let $C\in\mathbb Z^{q\times(q+r')}$ have full row rank $q$, with
--
--   $$
--   \|C\|_2\le 2^h,\qquad \sigma_{\min}(C)^{-1}\le 2^h .
--   $$
--
--   On input $(h,C)$, $\mathcal P$ is a Las Vegas procedure that outputs a unimodular $P\in\mathrm{GL}_{q+r'}(\mathbb Z)$ with $CP=[N,M]$, $N\in\mathbb Z^{q\times r'}$, $M\in\mathbb Z^{q\times q}$, such that
--
--   $$
--   \det M\ne0,\qquad \|M^{-1}N\|_2,\ \|P\|_2,\ \|P^{-1}\|_2\;\le\;(q+r'+1)^c,
--   $$
--
--   in expected $g(q+r',h)\,(q+r')^{\omega}\,h$ bit operations, input and output included.
--
--   The shear puts an integer residual block into a form whose last $q$ columns are nonsingular and dominate the others; the paper uses it to give integer coordinates to the quotient lattice (equation (14), Proposition 4.7).
--
--   **Formalization Note** Columns are indexed by $\{0,\dots,r'+q-1\}$: $N$ is the first $r'$ columns of $CP$ and $M$ the last $q$. "Polynomial in $q+r'$" is $(q+r'+1)^c$ with one exponent $c$ chosen with the program; $\widetilde O$ follows the conventions of §1.1.1 (p.4), as in the published goal: $\widetilde O$ suppresses a subpolynomial factor in the dimension and precision parameters, chosen with the program after $\omega$ and before every input. Las Vegas means every halting run is correct and the expected cost is bounded.
--
--   Differences from the source:
--   - encoding: C ∈ ℤ^{q×(q+r′)}, CP = [N, M] → C : Matrix (Fin q) (Fin (r′+q)) ℤ; N the first r′ and M the last q columns of CU; reason: same number of columns and the same split
--   - reading: poly(q+r′) bounds on ‖M⁻¹N‖₂, ‖P‖₂, ‖P⁻¹‖₂ → (q+r′+1)^c with c fixed with the program before the input; reason: for q+r′ ≥ 1 every polynomial is bounded by (q+r′+1)^c for some c
--   - reading: expected Õ((q+r′)^ω h) bit operations → LasVegasWithin with bound g(q+r′, h)(q+r′)^ω h, g subpolynomial, program reading (h, C); reason: the Õ convention of §1.1.1; h is a stated parameter of the procedure
--   - encoding: no size condition → 1 ≤ q + r′; reason: excludes only the empty matrix, where the bound is 0 and no run can meet it
-- source:
--   yang zhou, Mingsheng Wang, Zhedong Wang, Lattice Reduction at Average Precision, STOC 2027 submission #1574 (October 2026), Lemma 4.9, p.18 (proof App. B.2, pp.30–31)

import Definitions.Def_LatticeAvgPrec_OneVector_Supplement_Objects
open Matrix

namespace LatticeAvgPrec.OneVector.Supplement

/-- **Lemma 4.9** (A small integer shear; STOC 2027 submission #1574, p.18). Let
`C ∈ ℤ^{q×(q+r')}` have full row rank, with `‖C‖₂, σ_min(C)⁻¹ ≤ 2^h` and `h ≥ 1`. A Las Vegas
procedure computes a unimodular column transformation `P` taking `C` to `CP = [N, M]`, where `M` is
nonsingular and `‖M⁻¹N‖₂ ≤ poly(q+r')`; `P` and `P⁻¹` also have polynomial norm in `q+r'`. Its
expected cost is `Õ((q+r')^ω h)` bit operations.

**Formalization Note** The `q + r'` columns are indexed by `Fin (r' + q)`: `N` is the first `r'`
columns of `CP`, `M` the last `q`. The program receives `(h, C)` and writes the code of `P`.
`poly(q+r')` is `(q + r' + 1)^c` with one exponent `c` chosen with the program, after `ω` and
before every input; `Õ` is the subpolynomial factor `g(q+r', h)`. -/
theorem lemma_4_9 (ω : ℝ) (hω₁ : 2 < ω) (hω₂ : ω ≤ 3) (hM : MatMulAvailable ω) :
    ∃ (P : TimeSpaceMA.Program) (c : ℕ) (g : ℕ → ℕ → ℝ), IsSubpoly g ∧
      ∀ (q r' h : ℕ) (C : Matrix (Fin q) (Fin (r' + q)) ℤ), 1 ≤ q + r' → 1 ≤ h →
        (rmat C).rank = q → specNorm (rmat C) ≤ (2 : ℝ) ^ h →
        (sigmaMin (rmat C))⁻¹ ≤ (2 : ℝ) ^ h →
        SoftmaxAttnFD.LasVegasWithin P (TimeSpaceMA.memOf (natCode h ++ matCode C))
          (fun mem => ∃ U : Matrix (Fin (r' + q)) (Fin (r' + q)) ℤ,
            memHolds mem (matCode U) ∧ IsUnit U.det ∧
            ((C * U).submatrix id (Fin.natAdd r')).det ≠ 0 ∧
            specNorm ((rmat ((C * U).submatrix id (Fin.natAdd r')))⁻¹ *
                rmat ((C * U).submatrix id (Fin.castAdd q))) ≤ ((q : ℝ) + r' + 1) ^ c ∧
            specNorm (rmat U) ≤ ((q : ℝ) + r' + 1) ^ c ∧
            specNorm (rmat U)⁻¹ ≤ ((q : ℝ) + r' + 1) ^ c)
          (g (q + r') h * ((q + r' : ℕ) : ℝ) ^ ω * h) := by sorry

end LatticeAvgPrec.OneVector.Supplement
