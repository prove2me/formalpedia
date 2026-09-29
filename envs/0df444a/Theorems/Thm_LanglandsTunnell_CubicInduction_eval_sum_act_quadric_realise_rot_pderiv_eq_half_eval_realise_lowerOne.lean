-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_eval_sum_act_quadric_realise_rot_pderiv_eq_half_eval_realise_lowerOne
-- name    : LanglandsTunnell.CubicInduction.eval_sum_act_quadric_realise_rot_pderiv_eq_half_eval_realise_lowerOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/ff2f31ad-97c0-5433-98ca-750f7f3458df
-- title:
--   Symmetrised action on column realisations matches tfrac12 lower₁(Xi_ν p)
-- statement:
--   Fix $\nu\colon\{0,1,2\}\to\mathbb C$, an index $j\in\{0,1,2\}$ and a polynomial $p\in\mathbb C[x_0,x_1,x_2]$ which is harmonic, i.e. $\sum_i\partial_i\partial_i p=0$, and let $k\colon\{0,1,2\}^2\to\mathbb C$ satisfy $\sum_a k(i,a)k(j,a)=\delta_{ij}$, so that $k$ is an orthogonal $3\times 3$ matrix. Four operators are introduced. For $c,d$, $\mathrm{act}\,\nu\,c\,d$ acts on $\mathbb C[X_{(a,b)}]$ as multiplication by $\sum_a(\nu_a+w_a)X_{(a,c)}X_{(a,d)}$, where $w=(1,0,-1)$, plus the derivation $\sum_{i,j}\bigl(\sum_m \gamma^{(i)}_{m}\,X_{(m,j)}\bigr)\partial_{(i,j)}$ with $\gamma^{(i)}_m=X_{(i,c)}X_{(m,d)}$ for $m<i$, $-X_{(m,c)}X_{(i,d)}$ for $i<m$, and $0$ for $m=i$. The matrix $\Xi\,\nu\,p$ has diagonal entries $2(\nu_c+w_c)p$ and off-diagonal entries $-\bigl(x_{\max(c,d)}\partial_{\min(c,d)}p-x_{\min(c,d)}\partial_{\max(c,d)}p\bigr)$. The rotation operator is $\mathrm{rot}_a=\sum_{c,d}\tfrac{(a-c)(c-d)(d-a)}{2}\,x_c\partial_d$ (indices read as natural numbers in $\mathbb C$, the bracket being the Levi-Civita sign), and $\mathrm{lower}_1 M=\sum_{a,b}\mathrm{rot}_a\bigl(\partial_b M_{ab}\bigr)$. Finally $\mathrm{realise}$ is the algebra map $x_a\mapsto X_{(a,j)}$ onto the $j$-th column of variables. The assertion is the equality of values at $k$: the evaluation at $k$ of $\sum_{a,b,i,i'}\tfrac12\bigl(\mathrm{act}\,\nu\,a\,b+\mathrm{act}\,\nu\,b\,a\bigr)\bigl[\tfrac12(X_{(i,a)}X_{(i',b)}+X_{(i,b)}X_{(i',a)})\cdot\mathrm{realise}(\mathrm{rot}_{i'}\partial_i p)\bigr]$ equals the evaluation at $k$ of $\tfrac12\,\mathrm{realise}(\mathrm{lower}_1(\Xi\,\nu\,p))$.
--
--   This is the degree-lowering-by-one transition in the induced-picture computation for the principal series of $GL_3(\mathbb R)$ used in the Langlands–Tunnell step: the symmetrised quadratic action applied to the column realisation of $\mathrm{rot}_{i'}\partial_i p$ is identified, as a function on the orthogonal group rather than as a formal polynomial identity, with half the column realisation of $\mathrm{lower}_1(\Xi_\nu p)$. It feeds the extraction of the $\mathrm{lower}_1$ component of $\Xi$ from a sign-isotypic, respectively action-stable, reading of a polynomial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_eval_sum_act_quadric_realise_rot_pderiv_eq_half_eval_realise_lowerOne.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.eval_sum_act_quadric_realise_rot_pderiv_eq_half_eval_realise_lowerOne
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
    let lower₁ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
          (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) *
          (MvPolynomial.X c * MvPolynomial.pderiv b (MvPolynomial.pderiv d (M a b)))
    let rot : Fin 3 → MvPolynomial (Fin 3) ℂ → MvPolynomial (Fin 3) ℂ :=
      fun a q => ∑ c : Fin 3, ∑ d : Fin 3,
        MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
          (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) * (MvPolynomial.X c * MvPolynomial.pderiv d q)
    let realise : MvPolynomial (Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun q => MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)) q
    MvPolynomial.eval k
        (∑ a : Fin 3, ∑ b : Fin 3, ∑ i : Fin 3, ∑ i' : Fin 3,
          MvPolynomial.C (1 / 2 : ℂ) *
            (act ν a b (MvPolynomial.C (1 / 2 : ℂ) *
                (MvPolynomial.X (i, a) * MvPolynomial.X (i', b) + MvPolynomial.X (i, b) * MvPolynomial.X (i', a)) *
                realise (rot i' (MvPolynomial.pderiv i p))) +
             act ν b a (MvPolynomial.C (1 / 2 : ℂ) *
                (MvPolynomial.X (i, a) * MvPolynomial.X (i', b) + MvPolynomial.X (i, b) * MvPolynomial.X (i', a)) *
                realise (rot i' (MvPolynomial.pderiv i p))))) =
      MvPolynomial.eval k (MvPolynomial.C (1 / 2 : ℂ) * realise (lower₁ (Ξ ν p))) := by sorry
