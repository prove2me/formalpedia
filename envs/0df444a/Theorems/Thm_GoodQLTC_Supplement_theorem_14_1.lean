-- Prove2me | Theorems.Thm_GoodQLTC_Supplement_theorem_14_1
-- name    : GoodQLTC.Supplement.theorem_14_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:02:38.43799+00:00
-- url     : https://prove2.me/theorems/8dd79423-042b-487e-8cd2-8884f46147a5
-- title:
--   Theorem 14.1 — compatible Reed–Solomon cosheaves on the arithmetic quotients, uniformly product-expanding
-- statement:
--   Fix integers $t\ge4$, $r\ge3$, $h\ge1$ and $0\le a_1<\dots<a_t$, and fix $L\subseteq[t]$. Put $q_i:=2^{r+a_i}$, $n_i:=q_i+1$ and $\tau:=2^{a_t-a_1}$, and suppose
--   $$0<\epsilon<\frac1{D_h}<\beta<\frac12,\qquad \min_iq_i\ge Q_{\mathrm{end}}(h,\epsilon,\beta),$$
--   with $D_h=2^h+1$ and $Q_{\mathrm{end}}$ of (14.5). Then each quotient $X_\nu$ of the tower of Theorem 11.1 carries a cosheaf $\mathcal F_\nu$ over the field $\mathbb F=\mathbb F_{2^s}$ of (14.4), with compatible base codes whose dimensions $m_{i,b}$ are given by (14.3). For both $b\in\{0,1\}$,
--   $$\frac{m_{i,b}}{n_i}\in\begin{cases}[\epsilon,\beta],& i\in L,\\ [1-\beta,1-\epsilon],& i\notin L.\end{cases}$$
--   For every $f\in X_\nu$ and every nonempty $J\subseteq\mathrm{codir}(f)$, the family of local codes $\{C_{f,i}\}_{i\in J}$ is universally $\rho$-product-expanding with $\rho=\rho(t,\tau,\epsilon)>0$ as in (13.1). The same constant works after independently replacing any local code by its dual, and all these families have collective $\rho$-product expansion over every extension $\mathbb E/\mathbb F$. In particular, $\rho$ is independent of $r$ and $\nu$.
--
--   This supplies the input of the abstract construction (Theorem 4.12) and so, with Theorem 11.1, the explicit families of the Main Theorem.
--
--   **Formalization Note** The statement is proved for every quotient with the properties of Theorem 11.1 (1)–(2), not only the $X_\nu$ (see below). Cosheaf, base-code data, compatibility (4.4), local codes, duals, universal and collective product expansion are the published `GoodQLTC` definitions; $\rho$ is `GoodQLTC.rsRho t τ ϵ`. Dual replacement is a choice $c:[t]\to\{0,1\}$ ($c_i=1$: use $C_{f,i}^\perp$).
--
--   Differences from the source:
--   - generalization: the tower of Theorem 11.1 (the quotients X_ν = Γ_ν\∏_i T(K_{v_i})) → every orbit poset X = Γ\∏_i T(L_i) of a subgroup Γ ≤ ∏_i SL₂(L_i) acting freely on faces, for fields L_i with discrete valuation rings O_i whose residue fields have q_i elements, provided X is finite and a regular cubical complex with degrees n_i whose quotient map is an isomorphism on upward stars; reason: each X_ν of Theorem 11.1 is such a quotient (L_i = K_{v_i}, Γ the injective image of Γ_ν under x ↦ (φ_i(1 ⊗ x))_i), and the proof (pp.53–56) uses only these properties
--   - encoding: the field F_{2^s} of Equation (14.4) → every field F with |F| = 2^s; reason: all fields with 2^s elements are isomorphic to F_{2^s}
--   - encoding: universal and collective expansion over every extension E/F → extensions E in a universe u and coefficient spaces in a universe w, both left free; reason: the convention of the published IsUnivProductExpanding and HasCollectiveExpansion
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), Theorem 14.1, p.56 (PDF 59); Eqs. (14.3), (14.4), p.54; (14.5), p.55; (13.1), p.48

import Mathlib
import Definitions.Def_GoodQLTC_dir
import Definitions.Def_GoodQLTC_IsCubicalComplex
import Definitions.Def_GoodQLTC_IsRegular
import Definitions.Def_GoodQLTC_Cosheaf
import Definitions.Def_GoodQLTC_BaseCodeData
import Definitions.Def_GoodQLTC_IsProductExpanding
import Definitions.Def_GoodQLTC_HasCollectiveExpansion
import Definitions.Def_GoodQLTC_dualCode
import Definitions.Def_GoodQLTC_rsRho
import Definitions.Def_GoodQLTC_Supplement_ProductFace
import Definitions.Def_GoodQLTC_Supplement_endpointDims

namespace GoodQLTC.Supplement

open GoodQLTC
open scoped MatrixGroups

universe u w

/-- **Theorem 14.1** (compatible Reed–Solomon cosheaves on the tower), Gay–Jeronimo,
arXiv:2609.20780 (held version), p.56. Fix integers `t ≥ 4`, `r ≥ 3`, `h ≥ 1`,
`0 ≤ a_1 < ⋯ < a_t` and `L ⊆ [t]`; put `q_i := 2^{r+a_i}`, `n_i := q_i + 1`, `τ := 2^{a_t − a_1}`,
and suppose `0 < ϵ < 1/D_h < β < 1/2` and `min_i q_i ≥ Q_end(h, ϵ, β)`. Then every quotient `X`
of the tower carries a cosheaf over `F = F_{2^s}` (14.4) with compatible base codes of dimensions
(14.3); these satisfy `m_{i,b}/n_i ∈ [ϵ, β]` for `i ∈ L` and `∈ [1 − β, 1 − ϵ]` for `i ∉ L`
(`b ∈ {0, 1}`); for every `f ∈ X` and nonempty `J ⊆ codir(f)` the family `{C_{f,i}}_{i∈J}` is
universally `ρ`-product-expanding with `ρ = ρ(t, τ, ϵ)` of (13.1), the same `ρ` works after
independently replacing any local code by its dual, and all these families have collective
`ρ`-product expansion over every extension `E/F`.

**Formalization Note.** "The tower of Theorem 11.1" is generalized: the trees are `T(L_i)` for any
fields `L_i` with discrete valuation rings `O_i` whose residue fields have `q_i` elements, and `X`
is the orbit poset `Γ\T` (`IsOrbitQuotient`) of any subgroup `Γ ≤ ∏_i SL₂(L_i)` acting freely on the
faces of `T := ∏_i T(L_i)`, provided `X` is finite and, with the inherited labels, a regular cubical
complex with degrees `n_i` whose quotient map is an isomorphism on every upward star (Theorem 11.1
(1)–(2)). Each `X_ν` of Theorem 11.1 is such a quotient (`L_i = K_{v_i}`, `Γ` the image of `Γ_ν`
under `x ↦ (φ_i(1 ⊗ x))_i`, which is injective), so this implies the printed statement. `F` is any
field with `2^s` elements, `s = lcm{2(r + a_i)}`. `m i false = m_{i,0}`, `m i true = m_{i,1}`
(`endpointDims`). `ρ = rsRho t τ ϵ` (with `C(t, τ)` of p.46), the same for all `X`, `f`, `J`, dual
choices `c` (`c i = true`: replace `C_{f,i}` by `C_{f,i}^⊥`) and extensions `E` (of a universe `u`
left free; coefficient spaces of collective expansion in a universe `w`). "In particular, `ρ` is
independent of `r` and `ν`" is the remark that `rsRho t τ ϵ` involves only `t, τ, ϵ`. -/
theorem theorem_14_1 (t r h : ℕ) (a : Fin t → ℕ) (ht : 4 ≤ t) (hr : 3 ≤ r) (hh : 1 ≤ h)
    (ha : StrictMono a) (Lset : Finset (Fin t)) (ε β : ℝ) (hε : 0 < ε)
    (hεD : ε < 1 / (DH h : ℝ)) (hDβ : 1 / (DH h : ℝ) < β) (hβ : β < 1 / 2)
    (hQ : ∀ i, Qend h ε β ≤ (2 : ℝ) ^ (r + a i))
    (L : Fin t → Type) [∀ i, Field (L i)] (O : ∀ i, ValuationSubring (L i))
    [∀ i, IsDiscreteValuationRing (O i)]
    (hres : ∀ i, Nat.card (IsLocalRing.ResidueField (O i)) = 2 ^ (r + a i))
    (Γ : Subgroup (∀ i, SL(2, L i)))
    (hfree : ∀ γ ∈ Γ, ∀ f : ProductFace O,
      faceAct (fun i => Matrix.SpecialLinearGroup.toGL (γ i)) f.1 = f.1 → γ = 1)
    (X : Type) [PartialOrder X] [Fintype X] (p : ProductFace O → X)
    (φX : X → Fin t → Option Bool)
    (hX : IsOrbitQuotient (fun γ i => Matrix.SpecialLinearGroup.toGL (γ i))
      (Γ : Set (∀ i, SL(2, L i))) p φX)
    (hcc : IsCubicalComplex t φX) (hreg : IsRegular φX (fun i => 2 ^ (r + a i) + 1))
    (hstar : IsUpwardStarIso p)
    (F : Type) [Field F] [Fintype F] (hF : Fintype.card F = 2 ^ fieldExp r a) :
    ∃ (Fs : Cosheaf X F) (D : BaseCodeData φX Fs (endpointDims r h a Lset)),
      IsCompatible D ∧
      (∀ (i : Fin t) (b : Bool),
        (i ∈ Lset → ε ≤ (endpointDims r h a Lset i b : ℝ) / ((2 : ℝ) ^ (r + a i) + 1) ∧
          (endpointDims r h a Lset i b : ℝ) / ((2 : ℝ) ^ (r + a i) + 1) ≤ β) ∧
        (i ∉ Lset → 1 - β ≤ (endpointDims r h a Lset i b : ℝ) / ((2 : ℝ) ^ (r + a i) + 1) ∧
          (endpointDims r h a Lset i b : ℝ) / ((2 : ℝ) ^ (r + a i) + 1) ≤ 1 - ε)) ∧
      ∀ (f : X) (J : Finset (Fin t)), J.Nonempty → J ⊆ codir φX f → ∀ c : Fin t → Bool,
        IsUnivProductExpanding.{u}
          (rsRho t ((2 : ℝ) ^ (a ⟨t - 1, by omega⟩ - a ⟨0, by omega⟩)) ε)
          (fun i : J => if c i.1 then dualCode (localCode D f i.1) else localCode D f i.1) ∧
        ∀ (E : Type u) [Field E] [Algebra F E],
          HasCollectiveExpansion.{u, w} E
            (rsRho t ((2 : ℝ) ^ (a ⟨t - 1, by omega⟩ - a ⟨0, by omega⟩)) ε)
            (fun i : J => if c i.1 then dualCode (localCode D f i.1) else localCode D f i.1) := by sorry

end GoodQLTC.Supplement
