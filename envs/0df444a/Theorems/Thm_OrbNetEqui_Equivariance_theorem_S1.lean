-- Prove2me | Theorems.Thm_OrbNetEqui_Equivariance_theorem_S1
-- name    : OrbNetEqui.Equivariance.theorem_S1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:38:45.788007+00:00
-- url     : https://prove2.me/theorems/ccd5c4ee-4e99-4645-9c51-05640c151eac
-- title:
--   Theorem S1, p. 24 — a tensor product of irreducible unitary representations decomposes into catalogue irreducibles, with Σ_L μ(L) dim V^L = Π_j dim V^{L_j}
-- statement:
--   Let $K$ be a group and $(U^L)_{L\in\Lambda}$ a catalogue of irreducible unitary representations $U^L : K\to\mathrm U(\dim L)$ that is complete: every irreducible unitary representation of $K$ is equivalent to some $U^L$. Fix labels $L_1,\dots,L_N$ and let $K$ act on $\mathbb V^{L_1}\otimes\cdots\otimes\mathbb V^{L_N}$ by $k\mapsto U^{L_1}_k\otimes\cdots\otimes U^{L_N}_k$.
--
--   Then there are multiplicities $\mu(L)=\mu(L_1,\dots,L_N;L)\in\mathbb N$, nonzero for only finitely many $L$, and a linear isomorphism
--   $$\psi:\ \mathbb V^{L_1}\otimes\cdots\otimes\mathbb V^{L_N}\ \xrightarrow{\ \sim\ }\ \bigoplus_L\bigoplus_{\nu=1}^{\mu(L)}\mathbb V^{L;\nu}$$
--   such that $\psi\big((U^{L_1}_k\otimes\cdots\otimes U^{L_N}_k)T\big)_{L,\nu}=U^L_k\,\psi(T)_{L,\nu}$ for every $k\in K$, $L$ and $\nu$ (this is (S29)), and
--   $$\sum_L\mu(L)\dim\mathbb V^L=\prod_{j=1}^N\dim\mathbb V^{L_j}\qquad\text{(S30)}.$$
--
--   This is the decomposition on which the paper's diagonal reduction (Corollaries S2 and S3) rests.
--
--   **Formalization Note.** The paper states the theorem for $\mathrm U(n)$ and its irreducibles, citing [105], and remarks that it has "abstracted the labelling details for U(n) irreducible representations into the index L". Here $\mathrm U(n)$ is replaced by an arbitrary group $K$, and the labelling by the hypothesis `CatalogComplete`. Each catalogue member is assumed irreducible, as in Definition S2. The isomorphism (S29) is expressed by an equivariant linear equivalence onto $\prod_L(\mathbb C^{\dim L})^{\mu(L)}$.
-- source:
--   Qiao et al., Informing Geometric Deep Learning with Electronic Interactions to Accelerate Quantum Chemistry, arXiv:2105.14655v4, p. 24, Theorem S1, eqs. (S29)–(S30)

import Mathlib
import Definitions.Def_OrbNetEqui_Equivariance_Basic

namespace OrbNetEqui.Equivariance

open Matrix

theorem theorem_S1 {K : Type*} [Group K] {Λ : Type*} {dim : Λ → ℕ}
    (U : (L : Λ) → K →* Matrix.unitaryGroup (Fin (dim L)) ℂ)
    (hirr : ∀ L, IsIrreducibleUnitary (U L)) (hcat : CatalogComplete U)
    {N : ℕ} (Ls : Fin N → Λ) :
    ∃ (μ : Λ → ℕ) (s : Finset Λ), (∀ L, L ∉ s → μ L = 0) ∧
      (∃ ψ : (((j : Fin N) → Fin (dim (Ls j))) → ℂ) ≃ₗ[ℂ]
          ((L : Λ) → Fin (μ L) → Fin (dim L) → ℂ),
        ∀ (k : K) (T : ((j : Fin N) → Fin (dim (Ls j))) → ℂ) (L : Λ) (ν : Fin (μ L)),
          ψ (tensorProdAct (fun j => (U (Ls j) k : Matrix (Fin (dim (Ls j))) (Fin (dim (Ls j))) ℂ)) T)
              L ν =
            (U L k : Matrix (Fin (dim L)) (Fin (dim L)) ℂ) *ᵥ ψ T L ν) ∧
      ∑ L ∈ s, μ L * dim L = ∏ j, dim (Ls j) := by sorry

end OrbNetEqui.Equivariance
