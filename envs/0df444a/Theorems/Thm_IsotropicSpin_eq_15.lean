-- Prove2me | Theorems.Thm_IsotropicSpin_eq_15
-- name    : IsotropicSpin.eq_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:24:31.554193+00:00
-- url     : https://prove2.me/theorems/f357b67a-84f2-438c-8a47-4bcf76f570c9
-- title:
--   Eq. (15) — $S(\Lambda(|\phi\rangle\langle\phi|))=S(\Omega)$, $\Omega_{kl}=\langle\phi,X_l^\dagger X_k\phi\rangle$
-- statement:
--   Let $X_1,\dots,X_r$ be complex $n\times n$ matrices, $\Lambda(\rho)=\sum_k X_k\rho X_k^\dagger$, and $\phi\in\mathbb C^n$. Let $\Omega$ be the $r\times r$ matrix with entries $\Omega_{kl}=\langle\phi,X_l^\dagger X_k\phi\rangle$. Then
--
--   $$
--   S\big(\Lambda(|\phi\rangle\langle\phi|)\big)=S(\Omega),
--   $$
--
--   where $S(\sigma)=-\operatorname{tr}(\sigma\log\sigma)$ is the von Neumann entropy. The paper uses this identity, cited from its reference [2], with the Kraus operators $X_k=S_k/\sqrt{s(s+1)}$ of (6), which are Hermitian, so that $\Omega_{kl}=\langle\phi,X_lX_k\phi\rangle$.
--
--   It replaces the $n\times n$ output by the $r\times r$ matrix $\Omega$, whose operator norm is then bounded in (16).
--
--   **Formalization Note** No trace preservation of $\Lambda$ and no normalization of $\phi$ is assumed. $S$ is the published `WHAdditivity.Renyi.vonNeumannEntropy`.
--
--   Differences from the source:
--   - reading: Ω_kl = ⟨φ, X_l X_k φ⟩ with X_k the (unnamed) Kraus operators of Λ → Λ(|φ⟩⟨φ|) = Σ_k X_k |φ⟩⟨φ| X_k† and Ω_kl = ⟨φ, X_l† X_k φ⟩; reason: the page's X_k are the Hermitian Kraus operators S_k/√(s(s+1)) of (6), for which X_l† = X_l; the X_l† form is the one that holds for every Kraus family
--   - generalization: the channels (6) and a pure state |φ⟩ → any finite family X_k of square matrices and any vector φ; reason: the identity holds in this generality; it specializes to X_k = S_k/√(s(s+1)) and unit φ
--   - encoding: log (no base stated) → Real.log, the natural logarithm, inside the von Neumann entropy WHAdditivity.Renyi.vonNeumannEntropy (0 log 0 = 0); reason: Lean convention; every term of the statement scales by the same factor under a change of base
-- source:
--   Alicki, Isotropic quantum spin channels and additivity questions, arXiv:quant-ph/0402080v1, eq. (15), p.2

import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model

open scoped Matrix

namespace IsotropicSpin

/-- **Pure-input output entropy equals the entropy of `Ω`**, Alicki, arXiv:quant-ph/0402080v1,
eq. (15), p. 2 (cited there from [2]): for a channel `Λ(ρ) = Σ_k X_k ρ X_k†` and a vector `φ`,
`S(Λ(|φ⟩⟨φ|)) = S(Ω)` with `Ω_{kl} = ⟨φ, X_l† X_k φ⟩`.

**Formalization Note** Stated for every finite family of operators `X : κ → Matrix ι ι ℂ` and every
vector `φ` (no trace preservation and no normalization of `φ` is needed). The page writes
`Ω_{kl} = ⟨φ, X_l X_k φ⟩`, where the `X_k` are the Hermitian Kraus operators `S_k/√(s(s+1))` of
(6); for Hermitian `X_l` this is `⟨φ, X_l† X_k φ⟩`. `S` is the von Neumann entropy of the
published bundle `WHAdditivity.Renyi` (natural logarithm). -/
theorem eq_15 {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (X : κ → Matrix ι ι ℂ) (φ : ι → ℂ) :
    WHAdditivity.Renyi.vonNeumannEntropy (∑ k, X k * WHAdditivity.Renyi.pureState φ * (X k)ᴴ) =
      WHAdditivity.Renyi.vonNeumannEntropy
        (Matrix.of fun k l => star φ ⬝ᵥ (((X l)ᴴ * X k) *ᵥ φ)) := by sorry

end IsotropicSpin
