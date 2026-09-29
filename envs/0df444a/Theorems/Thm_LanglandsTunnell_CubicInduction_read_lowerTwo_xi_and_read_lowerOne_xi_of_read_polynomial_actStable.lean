-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_read_lowerTwo_xi_and_read_lowerOne_xi_of_read_polynomial_actStable
-- name    : LanglandsTunnell.CubicInduction.read_lowerTwo_xi_and_read_lowerOne_xi_of_read_polynomial_actStable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/fee123a2-fdd5-5b8a-91ef-dc5ffede2d92
-- title:
--   Reads of the two lowering transitions stay inside W
-- statement:
--   Fix $\nu \in \mathbb{C}^3$, a function $\varepsilon : \mathrm{Fin}\,3 \to \mathrm{Fin}\,2$, a $\mathbb{C}$-submodule $W$ of the polynomial ring in the nine variables $X_{ij}$ ($i,j \in \mathrm{Fin}\,3$), a natural number $\ell$, and a polynomial $p$ in three variables which is homogeneous of degree $\ell$ and harmonic, i.e. $\sum_i \partial_i \partial_i p = 0$. Four auxiliary data are introduced: the operator $\mathrm{act}\,\nu\,c\,d$ on nine-variable polynomials, given by multiplication by $\sum_a (\nu_a + s_a) X_{ac} X_{ad}$, where $s = (1,0,-1)$, plus $\sum_{i,j} \bigl(\sum_m \epsilon_{im}(c,d) X_{mj}\bigr)\partial_{(i,j)}$ with $\epsilon_{im}(c,d) = X_{ic}X_{md}$ for $m<i$, $-X_{mc}X_{id}$ for $i<m$ and $0$ for $m=i$; the matrix $\Xi\,\nu\,p$ with diagonal entries $2(\nu_c+s_c)\,p$ and off-diagonal entries $-\bigl(X_{\max(c,d)}\partial_{\min(c,d)}p - X_{\min(c,d)}\partial_{\max(c,d)}p\bigr)$; and the contractions $\mathrm{lower}_2(M) = \sum_{c,d}\partial_c\partial_d (M_{cd})$ and $\mathrm{lower}_1(M) = \sum_{a,b,c,d} \tfrac{(a-c)(c-d)(d-a)}{2}\,X_c\,\partial_b\partial_d(M_{ab})$, indices being read as complex numbers. Assume: $W$ is stable under every $\mathrm{act}\,\nu\,c\,d$; $W$ is stable under the substitutions $X_{ij} \mapsto \sum_c X_{ic}\,r_{cj}$ for every real matrix $r$ with $\sum_a r_{ai}r_{aj} = \delta_{ij}$; and there is $Q \in W$ with $Q(o) = \det(o)^{(\ell + \sum_a \varepsilon_a) \bmod 2}\, p(o_{\cdot 0})$ for every real orthogonal $o$, where $p(o_{\cdot 0})$ means $p$ with $X_a$ replaced by $X_{a0}$ and then evaluated at $o$. The conclusion is the conjunction of two statements of the same shape: there is $Q \in W$ reading as $\det(o)^{((\ell-2)+\sum_a\varepsilon_a)\bmod 2}$ times the zeroth-column read of $\mathrm{lower}_2(\Xi\,\nu\,p)$ on real orthogonal matrices, and likewise one reading as $\det(o)^{((\ell-1)+\sum_a\varepsilon_a)\bmod 2}$ times the zeroth-column read of $\mathrm{lower}_1(\Xi\,\nu\,p)$; the subtractions $\ell-2$, $\ell-1$ are truncated subtraction in $\mathbb{N}$.
--
--   This is the polynomial (compact-picture) form of the step which propagates the "read" property along the two lowering transitions of the cubic induction used in the Langlands–Tunnell input to the argument: from a space $W$ of polynomials in the entries of a $3\times 3$ matrix which is stable under the operators $\mathrm{act}\,\nu\,c\,d$ and under right multiplication by real orthogonal matrices, and in which a harmonic homogeneous $p$ of degree $\ell$ is read with the sign twist determined by $\varepsilon$, one obtains reads of the degree-$(\ell-2)$ and degree-$(\ell-1)$ lowerings $\mathrm{lower}_2(\Xi\,\nu\,p)$ and $\mathrm{lower}_1(\Xi\,\nu\,p)$. It is used in the construction of a transition-stable family of reads from an $\mathrm{act}$-stable, sign-isotypic one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_read_lowerTwo_xi_and_read_lowerOne_xi_of_read_polynomial_actStable.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.read_lowerTwo_xi_and_read_lowerOne_xi_of_read_polynomial_actStable
    (ν : Fin 3 → ℂ) (ε : Fin 3 → Fin 2) (W : Submodule ℂ (MvPolynomial (Fin 3 × Fin 3) ℂ))
    (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous ℓ)
    (hharm : (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) :
    let act : (Fin 3 → ℂ) → Fin 3 → Fin 3 →
        MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun ν c d p =>
        (∑ a : Fin 3, MvPolynomial.C (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) *
            (MvPolynomial.X (a, c) * MvPolynomial.X (a, d))) * p +
        ∑ i : Fin 3, ∑ j : Fin 3,
          (∑ m : Fin 3,
            (if m < i then MvPolynomial.X (i, c) * MvPolynomial.X (m, d)
              else if i < m then -(MvPolynomial.X (m, c) * MvPolynomial.X (i, d))
              else (0 : MvPolynomial (Fin 3 × Fin 3) ℂ)) * MvPolynomial.X (m, j)) *
            MvPolynomial.pderiv (i, j) p
    let Ξ : (Fin 3 → ℂ) → MvPolynomial (Fin 3) ℂ → Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) :=
      fun ν p => Matrix.of fun c d =>
        if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
        else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
          MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)
    let lower₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.pderiv c (MvPolynomial.pderiv d (M c d))
    let lower₁ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
          (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) *
          (MvPolynomial.X c * MvPolynomial.pderiv b (MvPolynomial.pderiv d (M a b)))
    (∀ P ∈ W, ∀ c d : Fin 3, act ν c d P ∈ W) →
    (∀ P ∈ W, ∀ r : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, r a i * r a j = if i = j then 1 else 0) →
        MvPolynomial.aeval (fun ij : Fin 3 × Fin 3 =>
            ∑ c : Fin 3, MvPolynomial.X (ij.1, c) * MvPolynomial.C ((r c ij.2 : ℝ) : ℂ)) P ∈ W) →
    (∃ Q ∈ W, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) Q =
          (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
            MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p)) →
    (∃ Q ∈ W, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) Q =
          (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ (((ℓ - 2) + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
            MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) (lower₂ (Ξ ν p)))) ∧
    (∃ Q ∈ W, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
        MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) Q =
          (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ (((ℓ - 1) + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
            MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) (lower₁ (Ξ ν p)))) := by sorry
