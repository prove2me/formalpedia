-- Prove2me | Theorems.Thm_ModularCurve_rep_tateModule_jOne_frickeAlgEquiv_transpose_diamond_galois_inertia_of_laws
-- name    : ModularCurve.rep_tateModule_jOne_frickeAlgEquiv_transpose_diamond_galois_inertia_of_laws
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/9f3b7720-2338-5e2a-b94c-62519f2e15b6
-- title:
--   Fricke laws on the Tate module of J₁(M)
-- statement:
--   Fix a natural number $M \neq 0$ and a prime $p$. Write $\bar F =$ `x1FunctionFieldBar M` for the field obtained by adjoining to $\overline{\mathbb Q}$, inside $\overline{\mathbb Q}((q))$, the coefficientwise images of the elements of the $\mathbb Q$-function field `x1FunctionField M` (the field generated over $\mathbb Q$ by $q$-expansions of ratios of integral modular forms for $\Gamma_1(M)$), and let `JOne M` $= \mathrm{Pic}^0(\overline{\mathbb Q}, \bar F)$ be the group of degree-zero divisor classes of $\bar F$ over $\overline{\mathbb Q}$, divisors being supported on the places of the definition `Place` (valuation subrings containing $\overline{\mathbb Q}$, proper, with principal ideals). The group `SemilinearAut` $(\overline{\mathbb Q}, \bar F)$ of pairs of ring automorphisms of $\bar F$ and of $\overline{\mathbb Q}$ compatible with the structure map acts on `JOne M`, and `SemilinearAut.ofAlgAut` sends a $\overline{\mathbb Q}$-algebra automorphism $u$ of $\bar F$ to the pair $(u, \mathrm{id})$; the group $\overline{\mathbb Q} \simeq_{\mathbb Q} \overline{\mathbb Q}$ acts on `JOne M` through the coefficients. The $p$-adic Tate module [`TateModule p (JOne M)`](def/EllipticCurve_TateModule.html#L15) is the group of sequences $x : \mathbb N \to$ `JOne M` with $p^n x_n = 0$ and $p\, x_{n+1} = x_n$, a $\mathbb Z_p$-module, and [`TateModule.rep`](def/EllipticCurve_TateModule.html#L174) attaches to an element of an acting monoid the $\mathbb Z_p$-linear endomorphism acting levelwise. For each $d$, `diamondOneBar M d` is the endomorphism of `JOne M` given by the action of $(\,$`diamondAutBar M d`$,\mathrm{id})$, where `diamondAutBar M d` is the base change to $\overline{\mathbb Q}$ of a chosen $\mathbb Q$-automorphism of `x1FunctionField M` satisfying `IsDiamondAut M d` (identity if none exists). Finally `HeckeAlgOne` is the polynomial ring $\mathbb Z[X_i]$ on indices $i \in$ `Nat.Primes` $\sqcup\ \mathbb N$, with generators `heckeGenOne ℓ` and `diamondGen d`, and `tateHeckeRepOne` is the induced ring homomorphism from `HeckeAlgOne` to $\mathbb Z_p$-endomorphisms of the Tate module; the conclusion is stated with the module structure `heckeModuleOneBar M` on `JOne M` installed, which, because `HeckeDiamondCommuteBar M` holds, sends `heckeGenOne ℓ` to `heckeOperatorOneBar M ℓ` and `diamondGen d` to `diamondOneBar M d`.
--
--   The hypotheses are: `hIn`, the assertion `HeckeDiamondInputsAll M`, i.e. for every prime $\ell$ the package `HeckeInputsOneAlong` over $\overline{\mathbb Q}$ (the $q \mapsto q^{\ell}$ degeneracy map is defined on `x1FunctionField M`, both degeneracy maps $\alpha, \beta$ into the base change of `x1x0FunctionFieldC ℚ M (M*ℓ)` are integral, that field has principal divisors, $\bar F$-finiteness along $\alpha$, the fundamental identity along $\beta$ and the pushforward norm formula along $\alpha$), together with, for every $d$ coprime to $M$, the existence of a diamond automorphism over $\mathbb Q$ and of an extension of it to $\bar F$ in the sense of `IsBaseChangeAutOf`; `hcomm`, the pairwise commutation of all the operators `heckeOperatorOneBar M ℓ` and `diamondOneBar M d` on `JOne M`; a $\overline{\mathbb Q}$-algebra automorphism $w$ of $\bar F$; and four laws for $w$ on divisor classes:
--
--   `htransp`: for every prime $\ell$, every integrality datum $h\alpha$ for `heckeAlphaOneBar` and $h\beta$ for `heckeBetaOneBar`, principal divisors on the base change of `x1x0FunctionFieldC ℚ M (M*ℓ)`, and every choice of the fundamental identity along $\beta$, finiteness along $\alpha$ and norm formula along $\alpha$, and symmetrically the fundamental identity along $\alpha$, finiteness along $\beta$ and norm formula along $\beta$, one has, for all $x$ in `JOne M`, that the transposed correspondence `heckePic0OneBarTranspose` (pullback along $\alpha$ followed by pushforward along $\beta$) applied to $w \cdot x$ equals $w \cdot$ (`heckePic0OneBar` applied to $x$, i.e. pullback along $\beta$ followed by pushforward along $\alpha$).
--
--   `hdiamond`: for all $d$ and all $x$, `diamondOneBar M d` $(w \cdot$ `diamondOneBar M d` $x) = w \cdot x$.
--
--   `hinv`: $w \cdot (w \cdot x) = x$ for all $x$.
--
--   `htwist`: for every $\sigma \in \overline{\mathbb Q} \simeq_{\mathbb Q} \overline{\mathbb Q}$ and every $c$ coprime to $M$ with $\sigma\zeta = \zeta^{c}$ for all $\zeta$ with $\zeta^{M} = 1$, and all $x$, $w \cdot (\sigma \cdot x) = \sigma \cdot ($`diamondOneBar M c`$(w \cdot x))$.
--
--   The conclusion is a conjunction of five assertions about the Tate module, all concerning the endomorphism [`TateModule.rep`](def/EllipticCurve_TateModule.html#L174) of $(w,\mathrm{id})$, written $W$ below, and the levelwise Galois endomorphisms.
--
--   First, $W \circ W$ is the identity: $W(W x) = x$ for every $x$ in [`TateModule p (JOne M)`](def/EllipticCurve_TateModule.html#L15).
--
--   Second, for every natural number $d$: the image of `diamondGen d` under `tateHeckeRepOne` is equal to [`TateModule.rep`](def/EllipticCurve_TateModule.html#L174) of the semilinear automorphism $(\,$`diamondAutBar M d`$, \mathrm{id})$; and for every $x$, the image of `diamondGen d` applied to $W$ applied to the image of `diamondGen d` applied to $x$ equals $W x$. No coprimality of $d$ with $M$ is required here.
--
--   Third, for every prime $\ell$, every integrality datum $h\alpha$, $h\beta$ and principal divisors on the base change of `x1x0FunctionFieldC ℚ M (M*ℓ)`, two statements hold. (a) For every choice of the fundamental identity along $\beta$, finiteness along $\alpha$ and norm formula along $\alpha$, every $x$ and every level $n$, the $n$-th component of `tateHeckeRepOne` of `heckeGenOne ℓ` applied to $x$ is `Pic0.correspondence` of $(\beta, \alpha)$ with these data applied to the $n$-th component of $x$; that is, $T_\ell$ acts on the Tate module levelwise by the Hecke correspondence. (b) For every choice of the fundamental identity along $\alpha$, finiteness along $\beta$ and norm formula along $\beta$, and every $\mathbb Z_p$-linear endomorphism $C'$ of the Tate module which acts levelwise by `Pic0.correspondence` of $(\alpha, \beta)$ with these data, one has $C'(W x) = W(\,$`tateHeckeRepOne` of `heckeGenOne ℓ` applied to $x)$ for every $x$; that is, $T_\ell^{t} W = W T_\ell$.
--
--   Fourth, a pair of compatibilities with the Galois action. (a) For every $\sigma \in \overline{\mathbb Q} \simeq_{\mathbb Q} \overline{\mathbb Q}$ and every natural number $c$ such that $\sigma \zeta = \zeta^{c}$ for all $\zeta$ with $\zeta^{M} = 1$, and every $x$, one has $W(\sigma \cdot x) = \sigma \cdot \big(\,$`tateHeckeRepOne` of `diamondGen c` applied to $W x\big)$, where $\sigma$ acts levelwise; unlike in `htwist`, $c$ is not assumed coprime to $M$. (b) If $\sigma$ fixes every $\zeta$ with $\zeta^{M} = 1$, then $W$ commutes with the levelwise action of $\sigma$.
--
--   Fifth, an inertia statement. Let $q$ be a prime with $q \mid M$ and $q^{2} \nmid M$, let $P$ be a valuation subring of $\overline{\mathbb Q}$ lying over $q$ in the sense that $q$ is a non-unit of $P$, and let $\tau$ belong to `P.inertiaSubgroupIn ℚ`, the image in $\overline{\mathbb Q} \simeq_{\mathbb Q} \overline{\mathbb Q}$ of the inertia subgroup of the decomposition subgroup of $P$. If $x$ in the Tate module satisfies, for every level $n$ and every $d$ in `normFreeRepsAt M q` (the $d < M$ coprime to $M$ with $d \equiv 1 \bmod M/q$), `diamondOneBar M d` applied to the $n$-th component of $x$ equals that component, then $W$ and the levelwise action of $\tau$ commute on $x$: $W(\tau \cdot x) = \tau \cdot (W x)$.
--
--   The statement transfers the four classical laws of a Fricke-type involution $w$ on $J_1(M)$ — commutation of $w$ with the Hecke correspondence up to transposition, the relation $\langle d\rangle w \langle d\rangle = w$, $w^2 = 1$, and the twisting law $w\sigma = \sigma\langle c\rangle w$ for $\sigma$ acting on $\mu_M$ by $c$ — from divisor classes to the $p$-adic Tate module, and adds that on the part of the Tate module fixed by the diamond operators indexed by residues $\equiv 1 \bmod M/q$ the induced involution commutes with inertia at a prime $q$ exactly dividing $M$. Here $w$ and its four laws are data rather than an existential conclusion; the result feeds the construction of a Hecke-equivariant bilinear form on the Tate module, with its self-adjointness, cyclotomic diamond behaviour and inertia properties, used in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_rep_tateModule_jOne_frickeAlgEquiv_transpose_diamond_galois_inertia_of_laws.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.rep_tateModule_jOne_frickeAlgEquiv_transpose_diamond_galois_inertia_of_laws
    (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hIn : HeckeDiamondInputsAll M) (hcomm : HeckeDiamondCommuteBar M)
    (w : x1FunctionFieldBar M ≃ₐ[AlgebraicClosure ℚ] x1FunctionFieldBar M)

    (htransp : ∀ (ℓ : ℕ) [Fact ℓ.Prime]
        (hα : HeckeAlphaOneBarIntegral (AlgebraicClosure ℚ) M ℓ)
        (hβ : HeckeBetaOneBarIntegral (AlgebraicClosure ℚ) M ℓ)
        [HasPrincipalDivisors (AlgebraicClosure ℚ)
          (laurentBaseChange (AlgebraicClosure ℚ) (x1x0FunctionFieldC ℚ M (M * ℓ)))]
        (hFIβ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
          (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ) hβ)
        (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ))
        (hNα : NormFormulaAlong (AlgebraicClosure ℚ)
          (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ) hfinα)
        (hFIα : FundamentalIdentityAlong (AlgebraicClosure ℚ)
          (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ) hα)
        (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ))
        (hNβ : NormFormulaAlong (AlgebraicClosure ℚ)
          (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ) hfinβ)
        (x : JOne M),
      heckePic0OneBarTranspose hα hβ hFIα hfinβ hNβ (SemilinearAut.ofAlgAut w • x)
        = SemilinearAut.ofAlgAut w • heckePic0OneBar hα hβ hFIβ hfinα hNα x)

    (hdiamond : ∀ (d : ℕ) (x : JOne M),
      diamondOneBar M d (SemilinearAut.ofAlgAut w • diamondOneBar M d x)
        = SemilinearAut.ofAlgAut w • x)

    (hinv : ∀ x : JOne M, SemilinearAut.ofAlgAut w • (SemilinearAut.ofAlgAut w • x) = x)

    (htwist : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ), c.Coprime M →
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) → ∀ x : JOne M,
        SemilinearAut.ofAlgAut w • (σ • x)
          = σ • diamondOneBar M c (SemilinearAut.ofAlgAut w • x)) :
    letI := heckeModuleOneBar M

    (∀ x : TateModule p (JOne M),
      TateModule.rep p (JOne M) (SemilinearAut (AlgebraicClosure ℚ) (x1FunctionFieldBar M))
          (SemilinearAut.ofAlgAut w)
        (TateModule.rep p (JOne M) (SemilinearAut (AlgebraicClosure ℚ) (x1FunctionFieldBar M))
          (SemilinearAut.ofAlgAut w) x) = x) ∧

    (∀ d : ℕ,
      tateHeckeRepOne p (JOne M) (diamondGen d) =
        TateModule.rep p (JOne M) (SemilinearAut (AlgebraicClosure ℚ) (x1FunctionFieldBar M))
          (SemilinearAut.ofAlgAut (diamondAutBar M d)) ∧
      ∀ x : TateModule p (JOne M),
        tateHeckeRepOne p (JOne M) (diamondGen d)
          (TateModule.rep p (JOne M) (SemilinearAut (AlgebraicClosure ℚ) (x1FunctionFieldBar M))
            (SemilinearAut.ofAlgAut w) (tateHeckeRepOne p (JOne M) (diamondGen d) x)) =
        TateModule.rep p (JOne M) (SemilinearAut (AlgebraicClosure ℚ) (x1FunctionFieldBar M))
          (SemilinearAut.ofAlgAut w) x) ∧

    (∀ (ℓ : ℕ) [Fact ℓ.Prime]
        (hα : HeckeAlphaOneBarIntegral (AlgebraicClosure ℚ) M ℓ)
        (hβ : HeckeBetaOneBarIntegral (AlgebraicClosure ℚ) M ℓ)
        [HasPrincipalDivisors (AlgebraicClosure ℚ)
          (laurentBaseChange (AlgebraicClosure ℚ) (x1x0FunctionFieldC ℚ M (M * ℓ)))],
      (∀ (hFIβ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ) hβ)
          (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ))
          (hNα : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ) hfinα)
          (x : TateModule p (JOne M)) (n : ℕ),
        ((tateHeckeRepOne p (JOne M) (heckeGenOne ⟨ℓ, Fact.out⟩) x : TateModule p (JOne M)) :
            ℕ → JOne M) n =
          Pic0.correspondence (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ)
            (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ) hβ hα hFIβ hfinα hNα
            ((x : ℕ → JOne M) n)) ∧
      (∀ (hFIα : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ) hα)
          (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ))
          (hNβ : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ) hfinβ)
          (C' : TateModule p (JOne M) →ₗ[ℤ_[p]] TateModule p (JOne M)),
        (∀ (b : TateModule p (JOne M)) (n : ℕ),
          ((C' b : TateModule p (JOne M)) : ℕ → JOne M) n =
            Pic0.correspondence (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ)
              (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ) hα hβ hFIα hfinβ hNβ
              ((b : ℕ → JOne M) n)) →
        ∀ x : TateModule p (JOne M),
          C' (TateModule.rep p (JOne M) (SemilinearAut (AlgebraicClosure ℚ) (x1FunctionFieldBar M))
              (SemilinearAut.ofAlgAut w) x) =
            TateModule.rep p (JOne M) (SemilinearAut (AlgebraicClosure ℚ) (x1FunctionFieldBar M))
              (SemilinearAut.ofAlgAut w)
              (tateHeckeRepOne p (JOne M) (heckeGenOne ⟨ℓ, Fact.out⟩) x))) ∧

    ((∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
        ∀ x : TateModule p (JOne M),
          TateModule.rep p (JOne M) (SemilinearAut (AlgebraicClosure ℚ) (x1FunctionFieldBar M))
              (SemilinearAut.ofAlgAut w)
              (TateModule.rep p (JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x) =
            TateModule.rep p (JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ
              (tateHeckeRepOne p (JOne M) (diamondGen c)
                (TateModule.rep p (JOne M)
                  (SemilinearAut (AlgebraicClosure ℚ) (x1FunctionFieldBar M))
                  (SemilinearAut.ofAlgAut w) x))) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ) →
        ∀ x : TateModule p (JOne M),
          TateModule.rep p (JOne M) (SemilinearAut (AlgebraicClosure ℚ) (x1FunctionFieldBar M))
              (SemilinearAut.ofAlgAut w)
              (TateModule.rep p (JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x) =
            TateModule.rep p (JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ
              (TateModule.rep p (JOne M)
                (SemilinearAut (AlgebraicClosure ℚ) (x1FunctionFieldBar M))
                (SemilinearAut.ofAlgAut w) x))) ∧

    (∀ (q : ℕ), q.Prime → q ∣ M → ¬ q ^ 2 ∣ M →
      ∀ (P : ValuationSubring (AlgebraicClosure ℚ)), P.LiesOverPrime q →
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ x : TateModule p (JOne M),
        (∀ (n : ℕ), ∀ d ∈ normFreeRepsAt M q,
          diamondOneBar M d ((x : ℕ → JOne M) n) = (x : ℕ → JOne M) n) →
        TateModule.rep p (JOne M) (SemilinearAut (AlgebraicClosure ℚ) (x1FunctionFieldBar M))
            (SemilinearAut.ofAlgAut w)
            (TateModule.rep p (JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) τ x) =
          TateModule.rep p (JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) τ
            (TateModule.rep p (JOne M) (SemilinearAut (AlgebraicClosure ℚ) (x1FunctionFieldBar M))
              (SemilinearAut.ofAlgAut w) x)) := by sorry
