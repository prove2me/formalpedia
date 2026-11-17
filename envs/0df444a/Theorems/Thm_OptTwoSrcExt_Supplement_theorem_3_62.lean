-- Prove2me | Theorems.Thm_OptTwoSrcExt_Supplement_theorem_3_62
-- name    : OptTwoSrcExt.Supplement.theorem_3_62
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:40:44.939896+00:00
-- url     : https://prove2.me/theorems/63586800-6e92-4625-8f19-7a58dfd5ab3a
-- title:
--   Theorem 3.62 — binary rank before the final seeds are revealed
-- statement:
--   Fix integers $m,t,J\ge1$, fields $F=\mathbb F_{2^m}\subset K=\mathbb F_{2^{4m}}\subset E=\mathbb F_{2^w}$ with $w=4mt$, a $K$-basis of $E$, the hash $H_J$ of (3.62), $B_*=Jt$, and the bias bounds of Lemma 3.59,
--   $$\beta=(B_*-1)2^{-4m},\qquad\gamma=(2J-2)2^{-w/2}.$$
--   Let $X,Y$ have product support $S_X\times S_Y$ (no independence is assumed). Suppose $Z$ and then $P$ are transcripts of deterministic communication between the $X$ and $Y$ sides, with $P$ a last left-side message, and write $\zeta=(Z,P)$. On each $\zeta$-leaf let $A=(A_i)_{i=0}^C$, $A_i\in E$, be functions of $X$ alone and $S=(S_i)_{i=0}^C$, $S_i\in K^2$, functions of $Y$ alone. Let $\{1,\dots,C\}=T\sqcup S$ and assume
--   $$(A_0,A_T,Z)\approx_\delta(U_E,A_T,Z),\tag{3.65}$$
--   $$(S_0,S_S,Z,P)\approx_\eta(U_{K^2},S_S,Z,P),\tag{3.66}$$
--   with uniform variables independent of the displayed ones. Assume $P$ has at most $2^\ell$ values for each value of $Z$, and
--   $$\beta<\tfrac12,\qquad\delta+2^{-3}+2^\ell\gamma+4\eta<1.\tag{3.67}$$
--   Then for every $\lambda_0\in F^*$ and $\lambda_1,\dots,\lambda_C\in F$, the matrix on the original product support $S_X\times S_Y$ with entries
--   $$M(x,y)=\mathrm{Tr}_{F/\mathbb F_2}\sum_{i=0}^C\lambda_iH_J(A_i;S_i)$$
--   has binary rank at least $Jw-\ell-3$.
--
--   The theorem shows that the final hash keeps almost all of its feature dimension after a short exposure, which is what guarantees rank against every comparison in the non-malleable rows.
--
--   **Formalization Note** The fields are any fields of the stated orders with algebra structures $\mathbb F_2\to F\to K\to E$, and the statement holds for every $K$-basis of $E$. $\{1,\dots,C\}$ is `Fin C` (shifted by one inside `Fin (C+1)`), $T$ any subset and $S$ its complement, either possibly empty. "A function of $X$ alone on each $\zeta$-leaf" is a function of $(\zeta,x)$. $\ell$ is real. Statistical distance is the published `statDist` under the joint law of $(X,Y)$.
--
--   Differences from the source:
--   - encoding: Z and then P transcripts of deterministic communication, P a last left-side message with at most 2^ℓ values per Z → Z = the transcript of a bitwise DetProtocol; P = Pmsg(Z, x), the number of its values over the support with transcript z at most 2^ℓ; reason: multi-bit messages are sequences of bits; a last left-side message is a function of the left input and the earlier transcript
--   - encoding: A_i functions of X alone and S_i functions of Y alone on each ζ-leaf → A i : (ζ, x) ↦ E and S i : (ζ, y) ↦ K × K, evaluated at ζ = (Z(x, y), P(Z, x)); reason: same functions, indexed by the leaf
--   - encoding: fields F = F_{2^m} ⊂ K = F_{2^{4m}} ⊂ E = F_{2^w} with a fixed K-basis → any fields of these cardinalities with algebra maps 𝔽₂ → F → K → E and any K-basis of E indexed by Fin t; reason: the statement is required for every such tower and basis; finite fields of a given order are unique up to isomorphism
--   - reading: P has at most 2^ℓ values for each Z (type of ℓ unstated) → ℓ : ℝ; reason: the real reading contains the integer one and the conclusion Jw − ℓ − 3 is read in ℝ
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Theorem 3.62, p.67 (PDF p.69); hash (3.62), p.65 (PDF p.67); Lemma 3.59, p.66 (PDF p.68)

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic
import Definitions.Def_LowErrExt_indepPair
import Definitions.Def_OptTwoSrcExt_rank2
import Definitions.Def_OptTwoSrcExt_Supplement_DetProtocol

open FuzzyExtractors.Hamming LowErrExt OptTwoSrcExt

namespace OptTwoSrcExt.Supplement

/-- **Theorem 3.62 (Rank before the final seeds are revealed).**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Theorem 3.62, printed p.67 (PDF p.69): "Let X, Y have
product support. Suppose Z and then P are transcripts of deterministic communication between the X
and Y sides, with P a last left-side message. Write ζ = (Z, P). On each ζ-leaf, let
A = (Ai)_{i=0}^C be functions of X alone, and S = (Si)_{i=0}^C functions of Y alone. Let
[C] = T ⊔ S and assume (A0, AT, Z) ≈δ (UE, AT, Z), (3.65) (S0, SS, Z, P) ≈η (UK2, SS, Z, P). (3.66)
Assume P has at most 2^ℓ values for each Z. Use the hash in (3.62) and suppose β < 1/2,
δ + 2^{−3} + 2^ℓγ + 4η < 1. (3.67) Then for every λ0 ∈ F∗ and λi ∈ F, the matrix on the original
product support with entries M(x, y) = Tr_{F/F2} Σ_{i=0}^C λi HJ(Ai; Si) has binary rank at least
Jw − ℓ − 3." The hash (3.62) and the setting are on printed p.65 (PDF p.67); β = (B∗ − 1)2^{−4m}
and γ = (2J − 2)2^{−w/2} are the bounds of Lemma 3.59, printed p.66 (PDF p.68).

Let `m, t, J ≥ 1`, `w = 4mt`, `F ⊂ K ⊂ E` fields of orders `2^m`, `2^{4m}`, `2^w`, `b` any
`K`-basis of `E` (indexed by `t` coordinates), `H_J = oddPowerHash b J`, `B∗ = Jt`,
`β = (B∗ − 1)2^{−4m}`, `γ = (2J − 2)2^{−w/2}`. Let `(X, Y)` have joint law `μ` on finite `α × β'`
with support `S_X × S_Y` (no independence assumed). Let `Z` be the transcript of a deterministic
protocol `π`, `P(z, x)` a further left message (a function of `x` and `Z`) taking at most `2^ℓ`
values on the support for each value `z` of `Z`, `ζ = (Z, P)`. Let `A_i(ζ, x) ∈ E` and
`S_i(ζ, y) ∈ K²` (`0 ≤ i ≤ C`), and split `{1, …, C}` into `T` and its complement `S`. If
`(A₀, A_T, Z) ≈_δ (U_E, A_T, Z)` and `(S₀, S_S, Z, P) ≈_η (U_{K²}, S_S, Z, P)` (uniform laws
independent of the displayed variables), `β < 1/2` and `δ + 2^{−3} + 2^ℓγ + 4η < 1`, then for every
`λ ∈ F^{C+1}` with `λ₀ ≠ 0` the `S_X × S_Y` matrix
`M(x, y) = Tr_{F/𝔽₂} Σ_{i=0}^C λ_i H_J(A_i(ζ(x, y), x); S_i(ζ(x, y), y))` has `𝔽₂`-rank at least
`Jw − ℓ − 3`.

**Formalization Note.** The fields are arbitrary fields of the stated orders with the algebra
structures `F → K → E` and `𝔽₂ → F` (any such tower; the statement is for every one and every
`K`-basis of `E`). The index `i ∈ {1, …, C}` is `Fin C` (`i ↦ i + 1` in `Fin (C + 1)`), `T` a subset
and `S = Tᶜ`, either possibly empty. "On each ζ-leaf a function of `X` alone" is a function of
`(ζ, x)`. No injectivity of `A_i`, `S_i` is assumed. Probabilities and distances are those of `μ`;
statistical distance is the published `statDist`. `ℓ` is real. -/
theorem theorem_3_62 {F K E : Type*} [Field F] [Field K] [Field E] [Fintype F] [Fintype K]
    [Fintype E] [Algebra (ZMod 2) F] [Algebra F K] [Algebra K E]
    (m t J : ℕ) (hm : 1 ≤ m) (ht : 1 ≤ t) (hJ : 1 ≤ J)
    (hF : Fintype.card F = 2 ^ m) (hK : Fintype.card K = 2 ^ (4 * m))
    (hE : Fintype.card E = 2 ^ (4 * m * t)) (b : Module.Basis (Fin t) K E)
    {α β' : Type*} [Fintype α] [Fintype β'] (μ : PMF (α × β'))
    (SX : Set α) (SY : Set β') (hsupp : μ.support = SX ×ˢ SY)
    (π : DetProtocol α β') (Pmsg : List Bool → α → List Bool) (ℓ : ℝ)
    (hP : ∀ z : List Bool, ({p | ∃ x ∈ SX, ∃ y ∈ SY, π.transcript x y = z ∧ Pmsg z x = p} :
      Set (List Bool)).ncard ≤ (2 : ℝ) ^ ℓ)
    (C : ℕ) (A : Fin (C + 1) → List Bool × List Bool → α → E)
    (S : Fin (C + 1) → List Bool × List Bool → β' → K × K) (T : Finset (Fin C))
    (δ η : ℝ)
    (h365 : statDist (μ.map fun p =>
        (A 0 (π.transcript p.1 p.2, Pmsg (π.transcript p.1 p.2) p.1) p.1,
          (fun i : T => A (i : Fin C).succ
            (π.transcript p.1 p.2, Pmsg (π.transcript p.1 p.2) p.1) p.1),
          π.transcript p.1 p.2))
      (indepPair (PMF.uniformOfFintype E) (μ.map fun p =>
        ((fun i : T => A (i : Fin C).succ
            (π.transcript p.1 p.2, Pmsg (π.transcript p.1 p.2) p.1) p.1),
          π.transcript p.1 p.2))) ≤ δ)
    (h366 : statDist (μ.map fun p =>
        (S 0 (π.transcript p.1 p.2, Pmsg (π.transcript p.1 p.2) p.1) p.2,
          (fun i : ↥(Tᶜ) => S (i : Fin C).succ
            (π.transcript p.1 p.2, Pmsg (π.transcript p.1 p.2) p.1) p.2),
          π.transcript p.1 p.2, Pmsg (π.transcript p.1 p.2) p.1))
      (indepPair (PMF.uniformOfFintype (K × K)) (μ.map fun p =>
        ((fun i : ↥(Tᶜ) => S (i : Fin C).succ
            (π.transcript p.1 p.2, Pmsg (π.transcript p.1 p.2) p.1) p.2),
          π.transcript p.1 p.2, Pmsg (π.transcript p.1 p.2) p.1))) ≤ η)
    (hβ : ((J * t : ℕ) - 1 : ℝ) * (2 : ℝ) ^ (-(4 * (m : ℝ))) < 1 / 2)
    (h367 : δ + (2 : ℝ) ^ (-3 : ℝ) +
      (2 : ℝ) ^ ℓ * ((2 * (J : ℝ) - 2) * (2 : ℝ) ^ (-((4 * m * t : ℕ) : ℝ) / 2)) + 4 * η < 1)
    (l : Fin (C + 1) → F) (hl : l 0 ≠ 0) :
    ((J * (4 * m * t) : ℕ) : ℝ) - ℓ - 3 ≤
      (rank2 (fun (x : SX) (y : SY) =>
        Algebra.trace (ZMod 2) F (∑ i : Fin (C + 1), l i *
          oddPowerHash b J
            (A i (π.transcript x.1 y.1, Pmsg (π.transcript x.1 y.1) x.1) x.1)
            (S i (π.transcript x.1 y.1, Pmsg (π.transcript x.1 y.1) x.1) y.1))) : ℝ) := by sorry

end OptTwoSrcExt.Supplement
