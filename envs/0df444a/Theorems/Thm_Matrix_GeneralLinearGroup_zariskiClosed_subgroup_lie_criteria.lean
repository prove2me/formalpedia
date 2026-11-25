-- Prove2me | Theorems.Thm_Matrix_GeneralLinearGroup_zariskiClosed_subgroup_lie_criteria
-- name    : Matrix.GeneralLinearGroup.zariskiClosed_subgroup_lie_criteria
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T15:55:15.546999+00:00
-- url     : https://prove2.me/theorems/506c4a2b-fb5b-52e3-b2ab-2b25184edab0
-- title:
--   Lie-algebra criteria for subgroups of $\mathrm{GL}_n$: finiteness when $\mathrm{Lie}(H)=0$, and $\mathrm{SL}_n$, $\mathrm{Sp}(B)$, $\mathrm{SO}(B)\subseteq H$ in characteristic $0$
-- statement:
--   Let $K$ be a field and $n \ge 0$. View $\mathrm{GL}_n(K)$ as the affine variety $\{(A, A') \in M_n(K)^2 : A A' = 1\}$, with coordinates the entries of $g$ and of $g^{-1}$, so its coordinate functions are polynomials $f$ in $2n^2$ variables. A subset $Z \subseteq \mathrm{GL}_n(K)$ is **Zariski closed** if it is the common zero set of a set of such polynomials. The **Lie algebra** of a subset $Z$ (for $1 \in Z$: the tangent space at $1$ of its Zariski closure) is
--
--   $$\mathrm{Lie}(Z) = \{X \in M_n(K) : D_{(X, -X)} f(1, 1) = 0 \text{ for every } f \text{ vanishing on } Z\},$$
--
--   where $D_{(X,-X)} f(1,1) = \sum_{i,j} \frac{\partial f}{\partial a_{ij}}(1,1) X_{ij} - \sum_{i,j} \frac{\partial f}{\partial a'_{ij}}(1,1) X_{ij}$ is the derivative at the identity in the direction of the curve $1 + \varepsilon X$ (whose inverse is $1 - \varepsilon X$ to first order). Let $H \le \mathrm{GL}_n(K)$ be a subgroup. Then:
--
--   1. (any field) if $\mathrm{Lie}(H) = 0$, then $H$ is finite ($H$ need not be closed here);
--   2. ($\mathrm{char}\, K = 0$) if $H$ is Zariski closed and $\mathrm{Lie}(H)$ contains every elementary matrix $E_{ij}$ ($i \ne j$), for instance if $\mathfrak{sl}_n \subseteq \mathrm{Lie}(H)$, then $\mathrm{SL}_n(K) \subseteq H$;
--   3. ($\mathrm{char}\, K = 0$) if $B \in M_n(K)$ is alternating ($B^T = -B$) and nondegenerate, $H$ is Zariski closed and $\mathfrak{sp}(B) = \{X : X^T B + B X = 0\} \subseteq \mathrm{Lie}(H)$, then $\mathrm{Sp}(B) = \{g : g^T B g = B\} \subseteq H$;
--   4. ($K$ algebraically closed of characteristic $0$, $n \ge 3$) if $B$ is symmetric and nondegenerate, $H$ is Zariski closed and $\mathfrak{so}(B) = \{X : X^T B + B X = 0\} \subseteq \mathrm{Lie}(H)$, then $\mathrm{SO}(B) = \{g : g^T B g = B,\ \det g = 1\} \subseteq H$.
--
--   Role: these are the two halves of the Lie-algebra method used to identify algebraic monodromy groups, for example in Larsen's alternative (a Zariski closed irreducible subgroup with small fourth moment is finite or contains $\mathrm{SL}_n$, $\mathrm{SO}(B)$ or $\mathrm{Sp}(B)$): one computes the Lie algebra of the identity component, and part 1 handles the case where it vanishes, parts 2 to 4 the case where it is the full classical Lie algebra. Part 1 is false for the Lie algebra of a non-reduced group scheme in characteristic $p$ ($\mu_p$ has a nonzero Lie algebra but only one point); here $\mathrm{Lie}$ is that of the reduced closure, and the statement holds in every characteristic. In parts 2 to 4 the characteristic $0$ hypothesis enters through exponentials of nilpotent elements of $\mathrm{Lie}(H)$: in characteristic $p$ the closed subgroup $\{1 + tE_{12} + t^p E_{13}\}$ of $\mathrm{GL}_3$ has Lie algebra $K E_{12}$ but does not contain $1 + tE_{12}$ for $t \ne 0$. In part 4 the bound $n \ge 3$ is what the proof uses (for $n \le 2$, $\mathrm{SO}(B)$ is a torus or trivial); smaller $n$ is not included.
--
--   **Formalization Note**: $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with rows and columns indexed by a finite type `n` ($n = $ `Fintype.card n`). The coordinate functions are `MvPolynomial ((n × n) ⊕ (n × n)) K`: the variable `Sum.inl (i, j)` is the entry $g_{ij}$ and `Sum.inr (i, j)` is the entry $(g^{-1})_{ij}$; `crd g` is the point of $K^{2n^2}$ given by these entries (pinned down by `hcrd`). `lie Z` is $\mathrm{Lie}(Z)$ (pinned down by `hlie`): `MvPolynomial.pderiv v f` is $\partial f / \partial x_v$, `crd 1` is the identity point, and `Sum.elim (fun ij => X ij.1 ij.2) (fun ij => -X ij.1 ij.2)` is the tangent vector $(X, -X)$. `IsZariskiClosed Z` (pinned down by `hclosed`) says that $Z$ is the zero set of a set `S` of polynomials. `crd`, `lie` and `IsZariskiClosed` are uniquely determined by `hcrd`, `hlie` and `hclosed`, which only abbreviate these formulas. `lie H ⊆ {0}` is $\mathrm{Lie}(H) = 0$ (the zero matrix always lies in it). `Matrix.single i j 1` is $E_{ij}$; `Matrix.SpecialLinearGroup.toGL M` is $M \in \mathrm{SL}_n(K)$ viewed in $\mathrm{GL}_n(K)$. `B.transpose = -B` is alternating (in characteristic $0$), `B.transpose = B` is symmetric, `B.Nondegenerate` is `Matrix.Nondegenerate`; `(g : Matrix n n K).transpose * B * g = B` is $g \in \mathrm{Sp}(B)$ resp. $g \in \mathrm{O}(B)$, and `(g : Matrix n n K).det = 1` adds $\det g = 1$. The characteristic and algebraic-closedness assumptions are the hypotheses `CharZero K` and `IsAlgClosed K` of the corresponding conjuncts. All types are in `Type`.
-- source:
--   J. E. Humphreys, Linear Algebraic Groups, Graduate Texts in Mathematics 21, Springer 1975, Sections 9 (Lie algebra of an algebraic group) and 13 (characteristic 0 theory); A. Borel, Linear Algebraic Groups, 2nd ed., Graduate Texts in Mathematics 126, Springer 1991, Chapter I, Section 3; N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in Contributions to Automorphic Forms, Geometry, and Number Theory, Johns Hopkins Univ. Press 2004, 521-560

import Mathlib

set_option autoImplicit false

theorem Matrix.GeneralLinearGroup.zariskiClosed_subgroup_lie_criteria
    (n : Type) [Fintype n] [DecidableEq n] (K : Type) [Field K]
    (crd : Matrix.GeneralLinearGroup n K → (n × n) ⊕ (n × n) → K)
    (hcrd : ∀ g, crd g = Sum.elim (fun ij => (g : Matrix n n K) ij.1 ij.2)
      (fun ij => ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) ij.1 ij.2))
    (lie : Set (Matrix.GeneralLinearGroup n K) → Set (Matrix n n K))
    (hlie : ∀ Z X, X ∈ lie Z ↔ ∀ f : MvPolynomial ((n × n) ⊕ (n × n)) K,
      (∀ g ∈ Z, MvPolynomial.eval (crd g) f = 0) →
        ∑ v, MvPolynomial.eval (crd 1) (MvPolynomial.pderiv v f) *
          Sum.elim (fun ij => X ij.1 ij.2) (fun ij => -X ij.1 ij.2) v = 0)
    (IsZariskiClosed : Set (Matrix.GeneralLinearGroup n K) → Prop)
    (hclosed : ∀ Z, IsZariskiClosed Z ↔ ∃ S : Set (MvPolynomial ((n × n) ⊕ (n × n)) K),
      ∀ g, g ∈ Z ↔ ∀ p ∈ S, MvPolynomial.eval (crd g) p = 0) :
    (∀ H : Subgroup (Matrix.GeneralLinearGroup n K), lie H ⊆ {0} → Finite H) ∧
    (CharZero K → ∀ H : Subgroup (Matrix.GeneralLinearGroup n K), IsZariskiClosed H →
      (∀ i j, i ≠ j → Matrix.single i j (1 : K) ∈ lie H) →
        ∀ M : Matrix.SpecialLinearGroup n K, Matrix.SpecialLinearGroup.toGL M ∈ H) ∧
    (CharZero K → ∀ B : Matrix n n K, B.transpose = -B → B.Nondegenerate →
      ∀ H : Subgroup (Matrix.GeneralLinearGroup n K), IsZariskiClosed H →
        (∀ X : Matrix n n K, X.transpose * B + B * X = 0 → X ∈ lie H) →
          ∀ g : Matrix.GeneralLinearGroup n K, (g : Matrix n n K).transpose * B * g = B → g ∈ H) ∧
    (CharZero K → IsAlgClosed K → 3 ≤ Fintype.card n →
      ∀ B : Matrix n n K, B.transpose = B → B.Nondegenerate →
      ∀ H : Subgroup (Matrix.GeneralLinearGroup n K), IsZariskiClosed H →
        (∀ X : Matrix n n K, X.transpose * B + B * X = 0 → X ∈ lie H) →
          ∀ g : Matrix.GeneralLinearGroup n K, (g : Matrix n n K).transpose * B * g = B →
            (g : Matrix n n K).det = 1 → g ∈ H) := by
  sorry
