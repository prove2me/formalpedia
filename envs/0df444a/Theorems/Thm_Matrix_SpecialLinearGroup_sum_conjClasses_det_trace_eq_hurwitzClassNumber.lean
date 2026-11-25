-- Prove2me | Theorems.Thm_Matrix_SpecialLinearGroup_sum_conjClasses_det_trace_eq_hurwitzClassNumber
-- name    : Matrix.SpecialLinearGroup.sum_conjClasses_det_trace_eq_hurwitzClassNumber
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-11-25T14:24:53.774498+00:00
-- url     : https://prove2.me/theorems/9e80ccf7-38b3-41ee-813b-497611418bb2
-- title:
--   Elliptic $\mathrm{SL}_2(\mathbb{Z})$-conjugacy classes of integer matrices of determinant $n$ and trace $t$, weighted by $1/\#\mathrm{centralizer}$, sum to $H(4n - t^2)$
-- statement:
--   Let $n$ and $t$ be integers with $t^2 < 4n$ (so $n \ge 1$), and let
--
--   $$\mathcal{M}_{n,t} = \left\{ \gamma = \begin{pmatrix} a & b \\ c & d \end{pmatrix} \in M_2(\mathbb{Z}) : \det \gamma = n,\ \operatorname{tr} \gamma = t \right\},$$
--
--   on which $\mathrm{SL}_2(\mathbb{Z})$ acts by conjugation $\gamma \mapsto g \gamma g^{-1}$. For $\gamma \in \mathcal{M}_{n,t}$ let $Z(\gamma) = \{ g \in \mathrm{SL}_2(\mathbb{Z}) : g\gamma = \gamma g \}$ be its centralizer, a finite group of order $2$, $4$ or $6$. Then
--
--   $$\sum_{[\gamma] \in \mathrm{SL}_2(\mathbb{Z}) \backslash \mathcal{M}_{n,t}} \frac{1}{\# Z(\gamma)} = H(4n - t^2),$$
--
--   the sum running over the (finitely many) conjugacy classes, where $H(N)$ is the Hurwitz class number: the number of $\mathrm{SL}_2(\mathbb{Z})$-classes of positive definite binary quadratic forms $a x^2 + b xy + c y^2$ (primitive or not) of discriminant $b^2 - 4ac = -N$, the classes of multiples of $x^2 + y^2$ and of $x^2 + xy + y^2$ counted with weight $\tfrac12$ and $\tfrac13$. Explicitly, $H(N) = \sum w(a, b, c)$ over the reduced triples, $b^2 - 4ac = -N$, $|b| \le a \le c$, and $b \ge 0$ if $|b| = a$ or $a = c$, with $w = \tfrac13$ if $a = b = c$, $w = \tfrac12$ if $b = 0$ and $a = c$, and $w = 1$ otherwise.
--
--   Moreover, the lower-left entry $c$ of $\gamma \in \mathcal{M}_{n,t}$ is never $0$ (if $c = 0$ then $t^2 - 4n = (a - d)^2 \ge 0$), its sign is a conjugacy invariant, and the classes with $c > 0$ and the classes with $c < 0$ each contribute exactly $\tfrac12 H(4n - t^2)$. For the classes with $c > 0$ this is the bijection $\gamma \mapsto [c, d - a, -b]$ (the form $v \mapsto \det(v, \gamma v)$) between $\mathrm{SL}_2(\mathbb{Z})$-classes of such matrices and classes of positive definite forms of discriminant $t^2 - 4n$, under which $Z(\gamma)$ is the automorphism group of the form; conjugation by $\mathrm{diag}(1, -1)$ exchanges the two signs.
--
--   For example, for $n = 1$, $t = 0$ there are two classes, those of $S = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$ and $S^{-1}$, each with a centralizer of order $4$, and $\tfrac14 + \tfrac14 = \tfrac12 = H(4)$; for $n = 1$, $t = 1$ the two classes have centralizers of order $6$ and $\tfrac16 + \tfrac16 = \tfrac13 = H(3)$; for $n = 2$, $t = 0$ the classes of $\begin{pmatrix} 0 & -2 \\ 1 & 0 \end{pmatrix}$ and $\begin{pmatrix} 0 & 2 \\ -1 & 0 \end{pmatrix}$ have centralizer $\{\pm I\}$ and $\tfrac12 + \tfrac12 = 1 = H(8)$.
--
--   Role: this is the class-number evaluation of the elliptic terms of the Eichler-Selberg trace formula at level one, where the elliptic conjugacy classes of determinant $n$ and trace $t$ contribute through $H(4n - t^2)$; its level-$M$ refinement (classes of $\Gamma_1(M)$) gives the elliptic terms of the trace formula for $T_n$ on $S_k(\Gamma_1(M))$.
--
--   **Formalization Note**: the conjugacy classes are `Quot` of the subtype of `Matrix (Fin 2) (Fin 2) ℤ` cut out by the conditions, by the relation $\gamma \sim \delta \iff \exists g \in \mathrm{SL}_2(\mathbb{Z}),\ g\gamma = \delta g$, which is already an equivalence relation (conjugacy), so the `Quot` is exactly the set of conjugacy classes; `C.out` is a chosen representative of the class `C`. The weight is `1 / Nat.card` of the centralizer subtype (a rational number), and `∑ᶠ` is `finsum`, an honest finite sum here since there are finitely many classes. `γ 1 0` is the lower-left entry $c$. $H(4n - t^2)$ is the variable `H` with the defining equation `hH`: a form is a triple `r : ℤ × ℤ × ℤ` with `r.1`, `r.2.1`, `r.2.2` the coefficients $a, b, c$, and the sum runs over the reduced triples of discriminant $t^2 - 4n$ in the box $[1, 4n] \times [-4n, 4n] \times [1, 4n]$, which contains all of them (a reduced form has $a \ge 1$, $|b| \le a \le c$ and $3ac \le 4n - t^2$); this is the same expression for $H(4n - t^2)$ as in `BinaryQuadraticForm.kronecker_hurwitz_class_number_relation`.
-- source:
--   D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Chapter 12 (Eichler-Selberg trace formula); H. Cohen, A Course in Computational Algebraic Number Theory, GTM 138, Springer 1993, Section 5.3 (Hurwitz class numbers and reduced forms)

import Mathlib

set_option autoImplicit false

open scoped MatrixGroups

theorem Matrix.SpecialLinearGroup.sum_conjClasses_det_trace_eq_hurwitzClassNumber
    (n : ℕ) (t : ℤ) (ht : t ^ 2 < 4 * (n : ℤ)) (H : ℚ)
    (hH : H = ∑ r ∈ (Finset.Icc (1 : ℤ) (4 * n) ×ˢ Finset.Icc (-(4 * n : ℤ)) (4 * n) ×ˢ
          Finset.Icc (1 : ℤ) (4 * n)).filter (fun r : ℤ × ℤ × ℤ =>
            r.2.1 ^ 2 - 4 * r.1 * r.2.2 = t ^ 2 - 4 * n ∧
              (|r.2.1| ≤ r.1 ∧ r.1 ≤ r.2.2 ∧ (|r.2.1| = r.1 ∨ r.1 = r.2.2 → 0 ≤ r.2.1))),
        (if r.1 = r.2.1 ∧ r.2.1 = r.2.2 then (1 / 3 : ℚ)
          else if r.2.1 = 0 ∧ r.1 = r.2.2 then 1 / 2 else 1)) :
    (∑ᶠ C : Quot (fun γ δ : {γ : Matrix (Fin 2) (Fin 2) ℤ // γ.det = n ∧ γ.trace = t} =>
        ∃ g : SL(2, ℤ), (g : Matrix (Fin 2) (Fin 2) ℤ) * γ.1 = δ.1 * g),
      (1 : ℚ) / Nat.card {g : SL(2, ℤ) // (g : Matrix (Fin 2) (Fin 2) ℤ) * C.out.1 = C.out.1 * g}) = H ∧
    (∑ᶠ C : Quot (fun γ δ : {γ : Matrix (Fin 2) (Fin 2) ℤ // γ.det = n ∧ γ.trace = t ∧ 0 < γ 1 0} =>
        ∃ g : SL(2, ℤ), (g : Matrix (Fin 2) (Fin 2) ℤ) * γ.1 = δ.1 * g),
      (1 : ℚ) / Nat.card {g : SL(2, ℤ) // (g : Matrix (Fin 2) (Fin 2) ℤ) * C.out.1 = C.out.1 * g}) =
        H / 2 ∧
    (∑ᶠ C : Quot (fun γ δ : {γ : Matrix (Fin 2) (Fin 2) ℤ // γ.det = n ∧ γ.trace = t ∧ γ 1 0 < 0} =>
        ∃ g : SL(2, ℤ), (g : Matrix (Fin 2) (Fin 2) ℤ) * γ.1 = δ.1 * g),
      (1 : ℚ) / Nat.card {g : SL(2, ℤ) // (g : Matrix (Fin 2) (Fin 2) ℤ) * C.out.1 = C.out.1 * g}) =
        H / 2 := by
  sorry
