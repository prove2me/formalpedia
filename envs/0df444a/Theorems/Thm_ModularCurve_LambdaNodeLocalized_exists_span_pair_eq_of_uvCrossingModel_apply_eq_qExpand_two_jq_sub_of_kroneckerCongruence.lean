-- Prove2me | Theorems.Thm_ModularCurve_LambdaNodeLocalized_exists_span_pair_eq_of_uvCrossingModel_apply_eq_qExpand_two_jq_sub_of_kroneckerCongruence
-- name    : ModularCurve.LambdaNodeLocalized.exists_span_pair_eq_of_uvCrossingModel_apply_eq_qExpand_two_jq_sub_of_kroneckerCongruence
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/2149812e-6919-505b-b9a5-a861f8fa419b
-- title:
--   Branch pins of the crossing model at j ∈ {0,1728}
-- statement:
--   Throughout, $q$ is a prime with $q \ge 5$, $A$ is a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, $k$ is a field of characteristic $q$ and $\mathrm{red} : A \to k$ is a ring homomorphism.
--
--   **The $j$-invariant and the $\lambda$-value.** An element $a \in k$ is given lying in `ssJSet q k`, i.e. such that for every Weierstrass curve $W$ over $k$ which is elliptic and has $W.j = a$, every point $P$ of the associated affine curve with $q \cdot P = 0$ is zero; moreover $a = 0$ or $a = 1728$. An element $l \in k$ is given with $l^{q^2} = l$, $l \neq 0$, $16l \neq 1$, and satisfying the level-two relation $a\,\bigl((16l)^2(16l-1)^2\bigr) = 256\,\bigl((16l)^2 - 16l + 1\bigr)^3$.
--
--   **The coefficient ring.** $K$ is an intermediate field of $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$, finite over $\mathbb{Q}$, and $A_0 :=$ `coeffSubring A K` is the intersection $A \cap K$ inside $\overline{\mathbb{Q}}$, with $\rho :=$ `redRestrict red K` the restriction of $\mathrm{red}$ to $A_0$. Elements $y, \varpi, \varepsilon \in A_0$ and a natural number $e_K \ge 1$ are given with $\rho(y) = l$; with $\varpi$ generating the kernel of $\rho$ in the strong sense that for every $c \in A_0$ one has $\rho(c) = 0$ if and only if $c = \varpi d$ for some $d \in A_0$; with $\varepsilon$ a unit; and with $q = \varpi^{e_K}\varepsilon$ in $A_0$.
--
--   **The node ring.** Write $S :=$ `lambdaLocalizedAtPoint q A₀ ρ l (l^q)`, the subring of Laurent series over $\overline{\mathbb{Q}}$ consisting of those $f$ for which there are $r, s \in A_0[X_0, X_1]$ with $f \cdot \mathrm{ev}(s) = \mathrm{ev}(r)$ and $s(l, l^q) \neq 0$ after applying $\rho$ to coefficients; here $\mathrm{ev} =$ `lambdaEval` is the evaluation sending $X_0$ to the $\lambda$-series `lambdaModC`, $X_1$ to its $q$-fold $q$-expansion `lambdaNModC _ q`, and a constant $o \in A_0$ to the corresponding constant Laurent series. The ring $S$ is assumed Noetherian and local. Abbreviate, for $P \in A_0[X_0,X_1]$, by $[P]$ the element $\mathrm{ev}(P)$ of $S$, and set $H := [X_0 - X_1^q]$, $G := [X_1 - X_0^q]$.
--
--   **The automorphism and its tangent action.** $g$ is a ring automorphism of $S$ with $g([C\,o]) = [C\,o]$ for every $o \in A_0$ (hypothesis `hgC`) and with $g^{[\,w\,]} = \mathrm{id}$, where $w :=$ `jWidth a` equals $3$ if $a = 0$, $2$ if $a = 1728$, and $1$ otherwise (hypothesis `hge`). Elements $\zeta_0, \zeta_0' \in A_0$ are given with $\rho(\zeta_0)^{w} = 1$, with $\rho(\zeta_0)^m \neq 1$ for all $0 < m < w$, and with $\rho(\zeta_0)\rho(\zeta_0') = 1$. Writing $\mathfrak{p} := ([C\,\varpi], [X_0 - C\,y], [X_1 - C\,(y^q)])$ for the ideal of $S$ spanned by these three elements, the hypotheses `htanH` and `htanG` require
--   $$g(H) - [C\,\zeta_0]\cdot H \in \mathfrak{p}^2 + (q), \qquad g(G) - [C\,\zeta_0']\cdot G \in \mathfrak{p}^2 + (q).$$
--
--   **The completion.** $\hat S$ denotes the completion of $S$ with respect to its maximal ideal, and $\hat g$ is a ring automorphism of $\hat S$ compatible with $g$ in the sense of `hĝ`: for every $n$, every $x \in \hat S$ and every $z \in S$, if the class of $z$ in $S/\mathfrak{m}^n$ is the $n$-th component of $x$, then the $n$-th component of $\hat g(x)$ is the class of $g(z)$.
--
--   **The two modular functions.** An element $x \in A_0$ is given with $\rho(x) = a$, and $J, Jq \in S$ are given whose underlying Laurent series are, respectively, the $2$-fold $q$-expansion of the $j$-series `jqModC` and the $2$-fold $q$-expansion of `jqNModC _ (1*q)` (the $j$-series expanded $q$-fold). Both are fixed by $g$: $g(J) = J$ and $g(Jq) = Jq$.
--
--   **The crossing model and the chart.** Let $W := A_0[[T]]/(T - C\,\varpi)$, let $\bar\varpi$ denote the class of $C\,\varpi$ in $W$, and let $\pi := \bar\varpi^{\,w\,e_K}$. Let $M :=$ `UVCrossingModel W π` $= W[[U,V]]/(UV - C\,\pi)$, with its distinguished elements `UVCrossingModel.U π` and `UVCrossingModel.V π` and its constants `UVCrossingModel.const π`. A ring homomorphism $\Phi : M \to \hat S$ is given, together with units $w_1, w_1'$ of $\hat S$ (named $w, w'$ in the statement), subject to: $\Phi$ is injective (`hΦinj`); the image of $\Phi$ is exactly the fixed locus of $\hat g$ (`hΦfix`); $\Phi$ carries the constant attached to $o \in A_0$ to the image of $[C\,o]$ in $\hat S$ (`hΦC`); and
--   $$\Phi(U\pi) = w_1 \cdot G^{\,w}, \qquad \Phi(V\pi) = w_1' \cdot H^{\,w}$$
--   in $\hat S$ (hypotheses `hΦU`, `hΦV`, the powers being taken of the images of $G$, $H$ under the structure map $S \to \hat S$).
--
--   **The crossing-model expressions for $J - x$ and $Jq - x^q$.** Units $c, c_q$ of $M$ and elements $r, r_q$ of $M$ are given with
--   $$r,\ r_q \in \bigl(\mathrm{const}\,\bar\varpi\bigr) + \bigl(\mathrm{const}\,\bar\varpi,\ U\pi,\ V\pi\bigr)^2$$
--   (hypotheses `hr`, `hrq`) and with
--   $$\Phi(c \cdot V\pi + r) = J - [C\,x], \qquad \Phi(c_q \cdot U\pi + r_q) = Jq - [C\,(x^q)]$$
--   in $\hat S$ (hypotheses `hcr`, `hcq`).
--
--   **The Kronecker congruence.** Finally, $(J^q - Jq)(J - Jq^{\,q}) \in q S$ (hypothesis `hKron`).
--
--   **Conclusion.** There exist $t, t' \in M$ such that
--   1. $\Phi(t)$ is the image of $Jq - J^{\,q}$ in $\hat S$;
--   2. $\Phi(t')$ is the image of $J - Jq^{\,q}$ in $\hat S$;
--   3. $\bigl(\mathrm{const}\,\bar\varpi,\ t\bigr) = \bigl(\mathrm{const}\,\bar\varpi,\ U\pi\bigr)$ as ideals of $M$;
--   4. $\bigl(\mathrm{const}\,\bar\varpi,\ t'\bigr) = \bigl(\mathrm{const}\,\bar\varpi,\ V\pi\bigr)$ as ideals of $M$,
--   where $\mathrm{const}\,\bar\varpi$ abbreviates `UVCrossingModel.const π` applied to the class of $C\,\varpi$ in $W$.
--
--   This is the branch-identification step for the crossing model of the node of $X_0(q)$ above a supersingular point with $j$-invariant $0$ or $1728$: the Kronecker congruence forces the two Frobenius graphs $Jq = J^{\,q}$ and $J = Jq^{\,q}$ to cut out, modulo $\varpi$, the two branches $U = 0$ and $V = 0$ of the model, so that each of $Jq - J^{\,q}$ and $J - Jq^{\,q}$ pins down one branch ideal. It is used in the construction of the ring isomorphism between the completed node ring and the crossing model, [`ModularCurve.exists_ringEquiv_adicCompletion_modularLocalizedAtPoint_uvCrossingModel_of_eq_zero_or_eq_1728`](thm.html#ModularCurve.exists_ringEquiv_adicCompletion_modularLocalizedAtPoint_uvCrossingModel_of_eq_zero_or_eq_1728).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LambdaNodeLocalized_exists_span_pair_eq_of_uvCrossingModel_apply_eq_qExpand_two_jq_sub_of_kroneckerCongruence.lean

import Mathlib
import Definitions.Def_ModularCurve_LambdaNodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open IsLocalRing ModularCurve ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized

theorem ModularCurve.LambdaNodeLocalized.exists_span_pair_eq_of_uvCrossingModel_apply_eq_qExpand_two_jq_sub_of_kroneckerCongruence
    {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (ha : a ∈ ssJSet q k) (h01728 : a = 0 ∨ a = 1728)
    (l : k) (hl2 : l ^ (q ^ 2) = l) (hl0 : l ≠ 0) (hl1 : 16 * l ≠ 1)
    (hla : a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (y : ↥(coeffSubring A K)) (hy : redRestrict red K y = l)
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (eK : ℕ) (ε : ↥(coeffSubring A K)) (heK : 1 ≤ eK) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε)
    [IsNoetherianRing ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))]
    [IsLocalRing ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))]

    (g : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ≃+* ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
    (hgC : ∀ o : ↥(coeffSubring A K), g (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C o),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) = (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C o),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))))
    (hge : ∀ z : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)), g^[jWidth a] z = z)

    (ζ₀ ζ₀' : ↥(coeffSubring A K))
    (hζe : redRestrict red K ζ₀ ^ jWidth a = 1)
    (hζprim : ∀ m : ℕ, 0 < m → m < jWidth a → redRestrict red K ζ₀ ^ m ≠ 1)
    (hζinv : redRestrict red K ζ₀ * redRestrict red K ζ₀' = 1)

    (htanH : g (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
          - (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ζ₀),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) * (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
        ∈ Ideal.span {(⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ϖ),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))), (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C y),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))),
            (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (y ^ q)),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))} ^ 2
          ⊔ Ideal.span {((q : ℕ) : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))})
    (htanG : g (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
          - (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ζ₀'),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) * (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
        ∈ Ideal.span {(⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ϖ),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))), (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C y),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))),
            (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (y ^ q)),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))} ^ 2
          ⊔ Ideal.span {((q : ℕ) : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))})

    (ĝ : AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ≃+* AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
    (hĝ : ∀ (n : ℕ) (x : AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) (z : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))),
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ^ n) z = AdicCompletion.evalₐ (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) n x →
        AdicCompletion.evalₐ (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) n (ĝ x) = Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ^ n) (g z))

    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (J Jq : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
    (hJ : (J : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) 2 (jqModC (AlgebraicClosure ℚ)))
    (hJq : (Jq : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) 2 (jqNModC (AlgebraicClosure ℚ) (1 * q)))

    (hgJ : g J = J) (hgJq : g Jq = Jq)

    (Φ : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) →+* AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
    (w w' : (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))ˣ)
    (hΦinj : Function.Injective Φ)
    (hΦfix : ∀ z : AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)), z ∈ Set.range Φ ↔ ĝ z = z)
    (hΦC : ∀ o : ↥(coeffSubring A K), Φ (UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) (Ideal.Quotient.mk _ (PowerSeries.C o)))
          = algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) _ (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C o),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))))
    (hΦU : Φ (UVCrossingModel.U (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))) = (w : AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) * (algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))) ^ jWidth a)
    (hΦV : Φ (UVCrossingModel.V (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))) = (w' : AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) * (algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))) ^ jWidth a)

    (c cq : (UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)))ˣ) (r rq : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)))
    (hr : r ∈ Ideal.span {UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ))} ⊔
        Ideal.span {UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)), UVCrossingModel.U (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)), UVCrossingModel.V (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))} ^ 2)
    (hrq : rq ∈ Ideal.span {UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ))} ⊔
        Ideal.span {UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)), UVCrossingModel.U (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)), UVCrossingModel.V (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))} ^ 2)
    (hcr : Φ ((c : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))) * UVCrossingModel.V (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) + r) =
        algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) (J - (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C x),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))))
    (hcq : Φ ((cq : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))) * UVCrossingModel.U (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) + rq) =
        algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) (Jq - (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C (x ^ q)),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))))

    (hKron : (J ^ q - Jq) * (J - Jq ^ q) ∈ Ideal.span {((q : ℕ) : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))}) :
    ∃ t t' : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)),
      Φ t = algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) (Jq - J ^ q) ∧
      Φ t' = algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) (J - Jq ^ q) ∧
      Ideal.span {UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)), t} =
        Ideal.span {UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)), UVCrossingModel.U (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))} ∧
      Ideal.span {UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)), t'} =
        Ideal.span {UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)), UVCrossingModel.V (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))} := by sorry
