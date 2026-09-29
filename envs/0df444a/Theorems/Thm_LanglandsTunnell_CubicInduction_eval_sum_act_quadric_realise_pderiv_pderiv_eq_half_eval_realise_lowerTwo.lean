-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_eval_sum_act_quadric_realise_pderiv_pderiv_eq_half_eval_realise_lowerTwo
-- name    : LanglandsTunnell.CubicInduction.eval_sum_act_quadric_realise_pderiv_pderiv_eq_half_eval_realise_lowerTwo
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/d7dca551-2ec1-57a5-aa7e-bd378e9929d3
-- title:
--   A degree-lowering identity on O(3) for the symmetrised action
-- statement:
--   Fix a vector $\nu\colon \mathrm{Fin}\,3 \to \mathbb{C}$, an index $j \in \mathrm{Fin}\,3$, a polynomial $p \in \mathbb{C}[X_0,X_1,X_2]$ that is harmonic in the sense that $\sum_i \partial_i\partial_i p = 0$, and a family $k\colon \mathrm{Fin}\,3 \times \mathrm{Fin}\,3 \to \mathbb{C}$ satisfying the orthogonality relations $\sum_a k(i,a)k(j,a) = \delta_{ij}$. Four auxiliary operators are introduced, with $w = (1,0,-1)$. For $c,d \in \mathrm{Fin}\,3$, $\mathrm{act}\,\nu\,c\,d$ is the operator on $\mathbb{C}[X_{(a,b)}]_{a,b}$ sending $q$ to $\bigl(\sum_a (\nu_a + w_a)X_{(a,c)}X_{(a,d)}\bigr)q + \sum_{i,l}\bigl(\sum_m A^{c,d}_{i,m} X_{(m,l)}\bigr)\,\partial_{(i,l)}q$, where $A^{c,d}_{i,m}$ is $X_{(i,c)}X_{(m,d)}$ for $m<i$, is $-X_{(m,c)}X_{(i,d)}$ for $i<m$, and vanishes for $m=i$. Next, $\Xi\,\nu\,p$ is the $3\times 3$ matrix over $\mathbb{C}[X_0,X_1,X_2]$ with diagonal entries $2(\nu_c+w_c)p$ and, for $c \neq d$, entry $-\bigl(X_{\max(c,d)}\partial_{\min(c,d)}p - X_{\min(c,d)}\partial_{\max(c,d)}p\bigr)$; $\mathrm{lower}_2$ sends a matrix $M$ to $\sum_{c,d}\partial_c\partial_d M_{cd}$; and $\mathrm{realise}$ is the algebra map $X_a \mapsto X_{(a,j)}$. The assertion is the equality, after evaluation of the polynomials in the variables $X_{(a,b)}$ at $k$, of $\sum_{a,b,i,i'} \tfrac12\bigl(\mathrm{act}\,\nu\,a\,b + \mathrm{act}\,\nu\,b\,a\bigr)\bigl[X_{(i,a)}X_{(i',b)}\,\mathrm{realise}(\partial_i\partial_{i'}p)\bigr]$ with $\tfrac12\,\mathrm{realise}\bigl(\mathrm{lower}_2(\Xi\,\nu\,p)\bigr)$. Note that this is an identity of values at orthogonal $k$, not an identity of polynomials.
--
--   This is one of the harmonic-projection identities used in the archimedean analysis of principal series of $GL_3(\mathbb{R})$ in the Langlands–Tunnell input: it matches the symmetrised raising action on a column realisation against the degree-lowering-by-two operator $\mathrm{lower}_2$ applied to the matrix $\Xi_\nu p$. It is used by the results that read off the $\mathrm{lower}_1$, $\mathrm{lower}_2$ and $\mathrm{same}_2$ components of $\Xi$ from sign-isotypic data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_eval_sum_act_quadric_realise_pderiv_pderiv_eq_half_eval_realise_lowerTwo.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.eval_sum_act_quadric_realise_pderiv_pderiv_eq_half_eval_realise_lowerTwo
    (ν : Fin 3 → ℂ) (j : Fin 3) (p : MvPolynomial (Fin 3) ℂ)
    (hharm : (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0)
    (k : Fin 3 × Fin 3 → ℂ)
    (hk : ∀ i j : Fin 3, (∑ a : Fin 3, k (i, a) * k (j, a)) = if i = j then 1 else 0) :
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
    let realise : MvPolynomial (Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun q => MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) q
    MvPolynomial.eval k
        (∑ a : Fin 3, ∑ b : Fin 3, ∑ i : Fin 3, ∑ i' : Fin 3,
          MvPolynomial.C (1 / 2 : ℂ) *
            (act ν a b (MvPolynomial.X (i, a) * MvPolynomial.X (i', b) *
                realise (MvPolynomial.pderiv i (MvPolynomial.pderiv i' p))) +
             act ν b a (MvPolynomial.X (i, a) * MvPolynomial.X (i', b) *
                realise (MvPolynomial.pderiv i (MvPolynomial.pderiv i' p))))) =
      MvPolynomial.eval k (MvPolynomial.C (1 / 2 : ℂ) * realise (lower₂ (Ξ ν p))) := by sorry
