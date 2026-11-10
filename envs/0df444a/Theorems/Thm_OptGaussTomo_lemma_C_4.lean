-- Prove2me | Theorems.Thm_OptGaussTomo_lemma_C_4
-- name    : OptGaussTomo.lemma_C_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:06:53.776125+00:00
-- url     : https://prove2.me/theorems/53bba8fc-b090-4b3a-9092-fdd08fdf3b71
-- title:
--   Lemma C.4 — $\dim\mathcal V^+_{n,m}=\dim\mathcal V^-_{n,m}=d_{n,m}$
-- statement:
--   For $s\in\{+,-\}$ let $\mathcal V^s_{n,m}$ be the span of the vectors $|\psi\rangle^{\otimes n}$ with $\psi\in\mathcal G^s_m$ a pure fermionic Gaussian state of parity $s$. Then for every $n\ge0$ and $m\ge1$
--
--   $$
--   \dim\mathcal V^+_{n,m}=\dim\mathcal V^-_{n,m}=d_{n,m}=\prod_{1\le j<k\le m}\frac{2m+n-(j+k)}{2m-(j+k)} .
--   $$
--
--   These dimensions control the Gaussian Hayashi measurement and the lower bound of Theorem 4.3.
--
--   Differences from the source:
--   - encoding: m modes → m ≥ 1; reason: an m-mode system has at least one mode; the paper writes m ∈ ℕ+ (Lemma D.14)
--   - encoding: V^±_{n,m}, the span of |ψ⟩^{⊗n} for |ψ⟩ ∈ G^±_m → the span of vecPow n ψ over unit vectors ψ ∈ gaussVecs m s; reason: same space
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), Lemma C.4 p.37 (pdf p.37), eq. (C.6)

import Mathlib
import Definitions.Def_OptGaussTomo_vecPow
import Definitions.Def_OptGaussTomo_gaussVecs
import Definitions.Def_OptGaussTomo_dFermi

open FermiCap.Gaussian (Qubits)

namespace OptGaussTomo

/-- **Lemma C.4** (Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, *Optimal tomography of
bosonic and fermionic Gaussian states*, arXiv:2607.11847, held version, sha256 0f7548a2…, Lemma C.4,
p.37). The two parity sectors have equal dimension, `dim V⁺_{n,m} = dim V⁻_{n,m} = d_{n,m}`, where
`d_{n,m} = ∏_{1≤j<k≤m} (2m + n − (j + k)) / (2m − (j + k))` (C.6). Here (p.37) `V^±_{n,m}` is the
span of `|ψ⟩^{⊗n}` for `|ψ⟩ ∈ G^±_m`.

**Formalization Note.** `G^±_m` is `gaussVecs m s` (`s = true`: even, `false`: odd) and
`|ψ⟩^{⊗n}` is `vecPow n ψ` in `ℂ^{(Qubits m)^n}`. The statement is for every `n ≥ 0` and every
`m ≥ 1` (an `m`-mode system has `m ≥ 1`; for `m = 0` there is no odd state). -/
theorem lemma_C_4 (m n : ℕ) (hm : 1 ≤ m) (s : Bool) :
    (Module.finrank ℂ (Submodule.span ℂ (vecPow n '' gaussVecs m s)) : ℝ) = dFermi n m := by sorry

end OptGaussTomo
