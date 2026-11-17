-- Prove2me | Theorems.Thm_HoneycombCodes_Supplement_theorem_4_4
-- name    : HoneycombCodes.Supplement.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:37:20.514829+00:00
-- url     : https://prove2.me/theorems/fb6ef104-6efa-4966-9616-70ec1407a563
-- title:
--   Theorem 4.4 — exact $B_n$ transition coefficients $p^\pm_{\sigma\tau}$ via the Wigner $6j$ symbol, and dimension balance
-- statement:
--   Fix $n$, $0\le k\le n/2$ and a box transfer of type $(\sigma,\tau)\in\{0,1\}^2$ from the valid triple $\omega=(i,j,\ell)$ to the valid triple $\omega'=(i+1,j-\sigma,\ell+\tau)$, so that $\lambda=(n-i-j,j)$, $\mu=(i-\ell,\ell)$ and the target partitions are $\lambda'=(n-i-1-(j-\sigma),j-\sigma)$, $\mu'=(i+1-(\ell+\tau),\ell+\tau)$. Let $V\cong V_{\lambda,\mu}$ and $V'\cong V_{\lambda',\mu'}$ be unitary irreducible representations of the hyperoctahedral group $B_n$, $E\cong S^{(n-k,k)}$ a unitary irreducible representation of $S_n\subseteq B_n$, $\phi:E\to V$ and $\phi':E\to V'$ isometric $S_n$-embeddings, $W=\mathbb C^n$ the natural signed representation and $\ell_o=n^{-1/2}(1,\dots,1)$. For isometric $B_n$-intertwiners $C^+:V'\to W\otimes V$ and $C^-:V\to W\otimes V'$, the contraction scalars $c^\pm$ are defined by (15):
--
--   $$
--   (C^+)^*(\ell_o\otimes\phi u)=c^+\phi'u,\qquad (C^-)^*(\ell_o\otimes\phi'u)=c^-\phi u\qquad(u\in E).
--   $$
--
--   Then the squared forward and reverse contraction coefficients $p^\pm_{\sigma\tau}(i,j,\ell;k)=|c^\pm|^2$ are
--
--   $$
--   p^+_{\sigma\tau}(i,j,\ell;k)=\frac{n-i}{n}\,\frac{f^{\lambda'}}{f^{\lambda}}\,R^2_{\sigma\tau},\qquad
--   p^-_{\sigma\tau}(i,j,\ell;k)=\frac{i+1}{n}\,\frac{f^{\mu}}{f^{\mu'}}\,R^2_{\sigma\tau},
--   $$
--
--   and, with $D_{i,j,\ell}=\binom ni f^{(n-i-j,j)}f^{(i-\ell,\ell)}$, one has exact dimension balance
--
--   $$
--   D_{i,j,\ell}\,p^+_{\sigma\tau}=D_{i+1,j-\sigma,\ell+\tau}\,p^-_{\sigma\tau}.
--   $$
--
--   Here $f^\theta=\dim S^\theta$ and $R_{\sigma\tau}=\sqrt{(2c+1)(2f+1)}\{\begin{smallmatrix}a&1/2&c\\d&e&f\end{smallmatrix}\}$ is the Wigner $6j$ factor with the spins (26). The theorem supplies the explicit directed weights and the balance identity that the finite honeycomb bound (Theorem 4.8) requires.
--
--   Differences from the source:
--
--   - encoding: $V_{\lambda,\mu}$ and $S^{(n-k,k)}$ → any irreducible of the type, characterized by nonzero intertwiners into the (colored) tabloid module and its sign twist (`IsBnType`, `IsSpechtType`); reason: these characterizations single out exactly the isomorphism classes $V_{\lambda,\mu}$, $S^\nu$ (Clifford theory and the Young-symmetrizer characterization), and $|c^\pm|$ does not depend on the chosen realization
--   - encoding: $p^\pm=(c^\pm)^2$ with phases chosen so that $c^\pm\ge0$ → $|c^\pm|^2$ (`Complex.normSq`) for arbitrary phases; reason: the same value
--   - encoding: (15), $C^*(\ell_o\otimes\phi u)=c\,\phi'u$ → its adjoint-free form $\langle Cv',\ell_o\otimes\phi u\rangle=c\langle v',\phi'u\rangle$ for all $v'$; reason: equivalent
--   - encoding: $f^\theta=\dim S^\theta$ for the two-row shapes → the published closed form `specht2 m r` $=\binom mr-\binom m{r-1}$; reason: the paper's own identity (36), (42) for two-row Specht modules
--   - encoding: "let $\lambda',\mu'$ be the target partitions for the edge $(\sigma,\tau)$" → hypotheses $\sigma\le j$ and the source and target triples valid; reason: the target partitions must exist, and when the target triple violates the triangle condition $E$ does not occur in $V'$, so no $\phi'$ exists and $p^\pm$ is $0$ only by the convention of Remark 4.7
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), §4.3, Theorem 4.4, p.22 (PDF 24); spins (26), p.18 (PDF 20); (15), p.14 (PDF 16)

import Mathlib
import Definitions.Def_HoneycombCodes_pDir
import Definitions.Def_HoneycombCodes_Supplement_wigner6j
import Definitions.Def_HoneycombCodes_Supplement_BnTypes

set_option autoImplicit false

open scoped InnerProductSpace TensorProduct

namespace HoneycombCodes.Supplement

/-- **Theorem 4.4 (exact transition coefficients)**, Gay, Granha Jeronimo, Liu, *The Honeycomb
Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), p.22 (PDF 24). Let
`λ = (n − i − j, j)`, `µ = (i − ℓ, ℓ)`, and let `λ′ = (n − i − 1 − (j − σ), j − σ)`,
`µ′ = (i + 1 − (ℓ + τ), ℓ + τ)` be the target partitions of the box transfer of type `(σ, τ)` from the
valid triple `ω = (i, j, ℓ)` to the valid triple `ω′ = (i + 1, j − σ, ℓ + τ)` at stabilizer type
`E = S^{(n−k, k)}` of `H = S_n ⊆ B_n`. The squared forward contraction coefficient is
`p⁺_{στ}(i, j, ℓ; k) = ((n − i)/n)(f_{λ′}/f_λ) R²_{στ}` (32), the squared reverse coefficient is
`p⁻_{στ}(i, j, ℓ; k) = ((i + 1)/n)(f_µ/f_{µ′}) R²_{στ}` (33), and, with
`D_{i,j,ℓ} = C(n, i) f_{(n−i−j, j)} f_{(i−ℓ, ℓ)}`, one has exact dimension balance
`D_{i,j,ℓ} p⁺_{στ} = D_{i+1,j−σ,ℓ+τ} p⁻_{στ}` (34). Here
`R_{στ} = √((2c + 1)(2f + 1)) {a ½ c; d e f}` with the spins (26).

The coefficients are those of (15), p.14: for unitary `B_n`-irreducibles `V ≅ V_{λ,µ}`,
`V′ ≅ V_{λ′,µ′}`, a unitary `S_n`-irreducible `E ≅ S^{(n−k,k)}`, isometric `S_n`-embeddings
`ϕ : E → V`, `ϕ′ : E → V′`, and isometric `B_n`-intertwiners `C⁺ : V′ → W ⊗ V` (forward) and
`C⁻ : V → W ⊗ V′` (reverse), with `W` the natural signed representation and
`ℓ_o = n^{−1/2}(1, …, 1)`, the scalars `c⁺, c⁻` are defined by
`(C⁺)*(ℓ_o ⊗ ϕ u) = c⁺ ϕ′ u` and `(C⁻)*(ℓ_o ⊗ ϕ′ u) = c⁻ ϕ u`, and `p± = |c±|²`.

**Formalization Note.** The `B_n`- and `S_n`-irreducibles are characterized intrinsically
(`IsBnType`, `IsSpechtType`); (15) is stated adjoint-free,
`⟪C⁺ v′, ℓ_o ⊗ ϕ u⟫ = c⁺ ⟪v′, ϕ′ u⟫` for all `v′`, `u`; the left-hand sides are these
representation-theoretic scalars, not the closed forms `pPlus`/`pMinus` of the base mission.
`f_{(m−r, r)}` is the published closed form `specht2 m r = C(m, r) − C(m, r − 1)` (eq. (36)),
`D_{i,j,ℓ}` the published `Domega`, validity the published `IsValidTriple` and the target triple
the published `target`. `R²_{στ}` is `RsqSixJ`, built from the Wigner 6j symbol by Racah's formula;
only its square enters, so the phase convention is irrelevant. -/
theorem theorem_4_4 (n k : ℕ) (hk : 2 * k ≤ n) (ω : ℕ × ℕ × ℕ) (σ τ : Fin 2)
    (hω : HoneycombCodes.IsValidTriple n k ω) (hσ : σ.val ≤ ω.2.1)
    (hω' : HoneycombCodes.IsValidTriple n k (HoneycombCodes.target ω σ τ))
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    {V' : Type*} [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
    (ρE : Representation ℂ (Equiv.Perm (Fin n)) E)
    (ρV : Representation ℂ (Bn n) V) (ρV' : Representation ℂ (Bn n) V')
    (ρW : Representation ℂ (Bn n) (EuclideanSpace ℂ (Fin n)))
    (hE : IsSpechtType ρE (twoRow (n - k) k))
    (hEu : ∀ (g : Equiv.Perm (Fin n)) (u u' : E), ⟪ρE g u, ρE g u'⟫_ℂ = ⟪u, u'⟫_ℂ)
    (hV : IsBnType ρV (twoRow (n - ω.1 - ω.2.1) ω.2.1) (twoRow (ω.1 - ω.2.2) ω.2.2))
    (hVu : ∀ (g : Bn n) (v v' : V), ⟪ρV g v, ρV g v'⟫_ℂ = ⟪v, v'⟫_ℂ)
    (hV' : IsBnType ρV' (twoRow (n - (ω.1 + 1) - (ω.2.1 - σ.val)) (ω.2.1 - σ.val))
      (twoRow (ω.1 + 1 - (ω.2.2 + τ.val)) (ω.2.2 + τ.val)))
    (hV'u : ∀ (g : Bn n) (v v' : V'), ⟪ρV' g v, ρV' g v'⟫_ℂ = ⟪v, v'⟫_ℂ)
    (hW : IsSignedNatural ρW)
    (ϕ : E →ₗ[ℂ] V) (ϕ' : E →ₗ[ℂ] V')
    (hϕ : ∀ u : E, ‖ϕ u‖ = ‖u‖) (hϕ' : ∀ u : E, ‖ϕ' u‖ = ‖u‖)
    (hϕeq : ∀ (π : Equiv.Perm (Fin n)) (u : E), ϕ (ρE π u) = ρV (SemidirectProduct.inr π) (ϕ u))
    (hϕ'eq : ∀ (π : Equiv.Perm (Fin n)) (u : E),
      ϕ' (ρE π u) = ρV' (SemidirectProduct.inr π) (ϕ' u))
    (Cf : V' →ₗ[ℂ] EuclideanSpace ℂ (Fin n) ⊗[ℂ] V)
    (Cr : V →ₗ[ℂ] EuclideanSpace ℂ (Fin n) ⊗[ℂ] V')
    (hCf : ∀ v : V', ‖Cf v‖ = ‖v‖) (hCr : ∀ v : V, ‖Cr v‖ = ‖v‖)
    (hCfeq : ∀ (g : Bn n) (v : V'), Cf (ρV' g v) = (ρW.tprod ρV) g (Cf v))
    (hCreq : ∀ (g : Bn n) (v : V), Cr (ρV g v) = (ρW.tprod ρV') g (Cr v))
    (cp cm : ℂ)
    (hcp : ∀ (u : E) (v' : V'), ⟪Cf v', ellO n ⊗ₜ[ℂ] ϕ u⟫_ℂ = cp * ⟪v', ϕ' u⟫_ℂ)
    (hcm : ∀ (u : E) (v : V), ⟪Cr v, ellO n ⊗ₜ[ℂ] ϕ' u⟫_ℂ = cm * ⟪v, ϕ u⟫_ℂ) :
    Complex.normSq cp =
        ((n : ℝ) - ω.1) / n *
          (HoneycombCodes.specht2 (n - ω.1 - 1) (ω.2.1 - σ.val) /
            HoneycombCodes.specht2 (n - ω.1) ω.2.1) * RsqSixJ n k σ τ ω ∧
      Complex.normSq cm =
        ((ω.1 : ℝ) + 1) / n *
          (HoneycombCodes.specht2 ω.1 ω.2.2 /
            HoneycombCodes.specht2 (ω.1 + 1) (ω.2.2 + τ.val)) * RsqSixJ n k σ τ ω ∧
      HoneycombCodes.Domega n ω * Complex.normSq cp =
        HoneycombCodes.Domega n (HoneycombCodes.target ω σ τ) * Complex.normSq cm := by sorry

end HoneycombCodes.Supplement
