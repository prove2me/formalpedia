-- Prove2me | Theorems.Thm_OptGaussTomo_lemma_C_5
-- name    : OptGaussTomo.lemma_C_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:08:45.649499+00:00
-- url     : https://prove2.me/theorems/a886b97d-2f02-4e62-86ef-ee3dcbf2634f
-- title:
--   Lemma C.5 — moments $\mathbf E F^{2(k-n)}=d_{n,m}/d_{k,m}$ of the Gaussian Hayashi measurement
-- statement:
--   Let $\psi\in\mathcal G_m$ ($m\ge1$) be a pure fermionic Gaussian state and let $\hat\psi$ be the outcome of the Gaussian Hayashi measurement $\mu_{n,m}$ applied to $\psi^{\otimes n}$. Write $F=|\langle\psi|\hat\psi\rangle|$. Then for every integer $k\ge1$
--
--   $$
--   \mathbf E\,F^{2(k-n)}=\mathbf E\,|\langle\psi|\hat\psi\rangle|^{2(k-n)}=\frac{d_{n,m}}{d_{k,m}}=\prod_{1\le i<j\le m}\frac{2m+n-(i+j)}{2m+k-(i+j)} .
--   $$
--
--   For $k<n$ the exponent is negative. These moments give the concentration of the fidelity in Corollary C.6.
--
--   **Formalization Note** The moment is an integral in $[0,\infty]$ of the integer power $(F^2)^{k-n}$; the event $F=0$ has probability zero.
--
--   Differences from the source:
--   - encoding: m modes → m ≥ 1; reason: an m-mode system has at least one mode; the paper writes m ∈ ℕ+ (Lemma D.14)
--   - encoding: the outcome ψ̂ of the POVM μ_{n,m} → an outcome (s, U) with ψ̂ = Uψ_s, distributed with density d_{n,m}|⟨ψ|Uψ_s⟩|^{2n} against counting × Haar (hayashiLaw); reason: this is the outcome law tr[dμ_{n,m}(φ)ψ^{⊗n}] of (C.7)
--   - encoding: E F^{2(k−n)} → a [0,∞]-valued integral with integer exponent k − n; reason: the exponent may be negative; no integrability condition is added and F = 0 is a null event
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), Lemma C.5 p.37 (pdf p.37)

import Mathlib
import Definitions.Def_WildeQIT_Schumacher_tensorPow
import Definitions.Def_OptGaussTomo_gaussVecs
import Definitions.Def_OptGaussTomo_dFermi
import Definitions.Def_OptGaussTomo_hayashiLaw

open FermiCap.Gaussian (Qubits Op)
open MeasureTheory
open scoped ENNReal

namespace OptGaussTomo

/-- **Lemma C.5** (Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, *Optimal tomography of
bosonic and fermionic Gaussian states*, arXiv:2607.11847, held version, sha256 0f7548a2…, Lemma C.5,
p.37). Let `ψ ∈ G_m` be a pure fermionic Gaussian state and `ψ̂` the outcome of the POVM `μ_{n,m}`
on the input `ψ^{⊗n}`. Then for every integer `k ≥ 1`,
`E F^{2(k−n)} = E |⟨ψ|ψ̂⟩|^{2(k−n)} = d_{n,m}/d_{k,m} = ∏_{1≤i<j≤m} (2m + n − (i+j))/(2m + k − (i+j))`.

**Formalization Note.** The outcome `(s, U)` of `μ_{n,m}` stands for `ψ̂ = U ψ_s`
(`hayashiLaw`), so `F = |⟨ψ|U ψ_s⟩|`. The input `ψ^{⊗n}` is the projector
`tensorPow n (|ψ⟩⟨ψ|)`. For `k < n` the exponent is negative; the moment is an `ℝ≥0∞`-valued
integral with the integer power `(F²)^{k−n}` (`0^{−j} = ⊤`), which needs no integrability side
condition (`F = 0` has probability zero under the outcome law, whose density contains `F^{2n}`).
The last equality of the source is the formula (C.6) for `d_{n,m}` (`dFermi`). `m ≥ 1` as for
every `m`-mode system. -/
theorem lemma_C_5 (m n k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) (ψ : Qubits m → ℂ)
    (hψ : ψ ∈ gaussVecs m true ∨ ψ ∈ gaussVecs m false) :
    ∫⁻ p, ((‖star ψ ⬝ᵥ (p.2 : Op m).mulVec (gaussRef m p.1)‖₊ : ℝ≥0∞) ^ 2) ^ ((k : ℤ) - n)
        ∂(hayashiLaw n m (WildeQIT.Schumacher.tensorPow n (Matrix.vecMulVec ψ (star ψ)))) =
      ENNReal.ofReal (dFermi n m / dFermi k m) := by sorry

end OptGaussTomo
